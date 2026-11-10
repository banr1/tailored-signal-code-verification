/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) — Part D

Proves `FreeOnlyEvs` error-cleanup exit tails (`+5368`, `+5360`, `+6904`, `+8588 -> s0.x30`) and the
post-`<PolyDecoder>::from_pb` tail (`+3044 -> s0.x30`) under `RustCliAllocBudget M`, re-exporting
stepping helpers from `Variant9dPlacedBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (Error PolynomialDecoder ProtoPolynomialDecoder pbToProtoPolyDecoder
   spqrAuthApi spqrPolyApi)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (boolByte polyDecoderAt resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved decoderFromPbResult epilogueStackGaps epilogueStackSlots overlapWord7
   resultChunkedStatesAt sp_sub_2400_align spqrErrorByte statesFromPbSavedCells
   statesFromPbStack v9_Saved5368Preserved v9_bs384_eq_decCells v9_bv_add_add_lit
   v9_ct1SentHeap v9_ct1SentHeap_entails_dealloc v9_decCellsAt
   v9_epilogueOutFull_entails_ct1Acknowledged v9_fsp_1888_entails_epilogue
   v9_fsp_6904_entails_2304 v9_fsp_8180_gaps_collapse v9_fsp_8588_entails_2304
   v9_loBytes7_64_313_entails_bs328 v9_memRegion_3044_collapse_err v9_memRegion_3044_split_ok
   v9_midQ128 v9_optProtoPolyDecoderHeap v9_polyDecoderAt_relocate v9_quadAt
   v9_stackAt_allocHook_to_encoderFromPbStack v9_stackAt_encoderFromPbStack_to_allocHook
   v9_wordAt v9_zext32_setWidth8)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlacedBudget
  (v9_states_from_pb_dealloc_none_proto_decoder_5360_placed_budget
   v9_states_from_pb_dealloc_proto_decoder_5368_of_sub_placed
   v9_states_from_pb_dealloc_some_proto_decoder_5360_of_sub_placed
   v9_states_from_pb_drop_uc_6904_of_sub_placed
   v9_states_from_pb_drop_uc_8588_of_sub_placed
   v9_sub_ok_dealloc_of_dealloc_placed)

export Variant9dPlacedBudgetAux
  (v9_auth_from_pb_pinned_placed_ok_of_sub v9_auth_from_pb_pinned_placed_ok
   v9_auth_from_pb_pinned_cl_on)
export Variant9dPlacedBudgetAux
  (v9_step_2864_ok_some_to_3040_placed v9_step_2864_ok_some_to_3040_placed_budget
   v9_step_3044_err_to_8588_placed v9_step_3044_err_to_8588_placed_budget)
export Variant9dPlacedBudgetAux
  (v9_step_3044_ok_to_8180_placed v9_step_3044_ok_to_8180_placed_budget
   v9_seq_err_7084_placed v9_seq_err_7084_evs_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

private theorem strengthen_evs_post {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {R1 R2 : List AllocEvent → State → SepProp} {Q : State → Prop}
    (hent : ∀ (evs : List AllocEvent) (sm : State), R1 evs sm ⊢ R2 evs sm)
    (h : SepWP prog target s P (fun sm Pm =>
      ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ (Pm ⊢ R1 evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧ (Pm ⊢ R2 evs sm) ∧ Q sm) :=
  SepWP.mono h fun sm _Pm _ _ ⟨evs, hevs, hPm, hQ⟩ =>
    ⟨evs, hevs, Entails.trans hPm (hent evs sm), hQ⟩

/-! ## 1. Error-Cleanup Exit Tails (`+5368`, `+5360`, `+6904`, `+8588 -> s0.x30`) -/

/-- From `+5368` (`dealloc_proto_decoder_5368`) through `+7084` (`err_7084`) to `s0.x30`
    when `receivingEk = some d` is still live in `v9_optProtoPolyDecoderHeap`. -/
theorem v9_tail_5368_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (d : ProtoPolynomialDecoder) (err : Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A.repAlloc (some d) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, _hp_ne, _hw32⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
      (Entails.of_eq (show _ =
        (if w0 = 0#64 then emp
         else A.repAlloc.live w8 (w0.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 w8 d.pts ∗
           memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        by sep_ac_rfl))) ?_
  refine v9_seq_err_7084_evs_placed A lim st (F := F) s0 s fsp out pbA _ err hsp0_align hfsp_eq
    (strengthen_evs_post ?_
      (v9_states_from_pb_dealloc_proto_decoder_5368_of_sub_placed hdealloc_ok st s0 s fsp out
        w8 w0 x28_val d.pts
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hle hcap hpc hrun hpres hx22))
    (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
  intro evs sm
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    A.pool lim (M.stepEvents evs st) sm ∗ memRegion pbA optProtoInnerStateSize by sep_ac_rfl)) ?_
  exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

theorem v9_tail_5368_to_ret_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (d : ProtoPolynomialDecoder) (err : Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A.repAlloc (some d) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_5368_to_ret_of_sub_placed (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out pbA w0 w8 w16 d24 d28 w32 x28_val d err
    hsp0_align hfsp_eq hpc hrun hpres hx22 herr

theorem v9_tail_5368_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (d : ProtoPolynomialDecoder) (err : Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A.repAlloc (some d) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_5368_to_ret_of_dealloc_placed hA.dealloc
    st s0 s fsp out pbA w0 w8 w16 d24 d28 w32 x28_val d err
    hsp0_align hfsp_eq hpc hrun hpres hx22 herr

/-- From `+5360` (`dealloc_none/some_proto_decoder_5360`) through `+7084` (`err_7084`) to `s0.x30`
    for arbitrary `optDec : Option ProtoPolynomialDecoder`. -/
theorem v9_tail_5360_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (err : Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A.repAlloc optDec w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases optDec with
  | none =>
    dsimp only [v9_optProtoPolyDecoderHeap]
    apply SepWP.pure_elim; rintro rfl
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      A.pool lim st s ∗
      (memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
       memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      by sep_ac_rfl)) ?_
    have hnone := v9_seq_err_7084_placed A lim st (F := F) s0 s fsp out pbA _ err
      hsp0_align hfsp_eq
      (SepWP.mono
        (v9_states_from_pb_dealloc_none_proto_decoder_5360_placed_budget A lim st (ext := ext)
          s0 s fsp out w8 x28_val
          (memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hpc hrun hpres)
        fun sm Pm _ _ ⟨hPm, _hvm, hpres_m⟩ =>
          ⟨Entails.trans hPm (by subst hfsp_eq; exact Entails.of_eq (by sep_ac_rfl)), hpres_m⟩)
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    refine SepWP.mono hnone fun sf Pf _ _ ⟨hPf, hrest⟩ => ?_
    exact ⟨[], FreeOnlyEvs.nil, by simpa only [M.stepEvents_nil] using hPf, hrest⟩
  | some d =>
    dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, _hp_ne, _hw32⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
        (Entails.of_eq (show _ =
          (if w0 = 0#64 then emp
           else A.repAlloc.live w8 (w0.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 w8 d.pts ∗
             memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          by sep_ac_rfl))) ?_
    refine v9_seq_err_7084_evs_placed A lim st (F := F) s0 s fsp out pbA _ err hsp0_align hfsp_eq
      (strengthen_evs_post ?_
        (v9_states_from_pb_dealloc_some_proto_decoder_5360_of_sub_placed hdealloc_ok st s0 s fsp out
          w8 w0 x28_val d.pts
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hfsp_align hle hcap hpc hrun hpres hx22))
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    intro evs sm
    subst hfsp_eq
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
      memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs st) sm ∗ memRegion pbA optProtoInnerStateSize by sep_ac_rfl)) ?_
    exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

theorem v9_tail_5360_to_ret_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (err : Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A.repAlloc optDec w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_5360_to_ret_of_sub_placed (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out pbA w0 w8 w16 d24 d28 w32 x28_val optDec err
    hsp0_align hfsp_eq hpc hrun hpres hx22 herr

theorem v9_tail_5360_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (err : Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A.repAlloc optDec w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_5360_to_ret_of_dealloc_placed hA.dealloc
    st s0 s fsp out pbA w0 w8 w16 d24 d28 w32 x28_val optDec err
    hsp0_align hfsp_eq hpc hrun hpres hx22 herr

/-- From `+6904` (`drop_uc_6904`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_6904_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr) (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap) (hx13 : s.readReg64 .x13 = ct1Cap)
    (hx14 : s.readReg64 .x14 = ct1Ptr) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A.repAlloc (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ A.pool lim st s ∗ memRegion fsp 72 ∗
     memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize) by sep_ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗
    vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗ vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
    vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗ vecCapPtrDealloc A.repAlloc esCap esPtr ∗
    vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
  refine v9_seq_err_7084_evs_placed A lim st (F := F) s0 s fsp out pbA _ .stateDecode
    hsp0_align hfsp_eq
    (strengthen_evs_post ?_
      (v9_states_from_pb_drop_uc_6904_of_sub_placed hdealloc_ok st s0 s fsp out
        rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
         memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  intro evs sm
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 72 ∗ ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗
     memRegion (s0.sp - 2400#64 + 80#64) 48 ∗ ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗
     memRegion (s0.sp - 2400#64 + 136#64) 8 ∗ ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗ memRegion (s0.sp - 2400#64 + 160#64) 2144) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    A.pool lim (M.stepEvents evs st) sm ∗ memRegion pbA optProtoInnerStateSize by sep_ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_6904_entails_2304 (s0.sp - 2400#64) esPtr esCap hdrPtr hdrCap))

theorem v9_tail_6904_to_ret_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr) (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap) (hx13 : s.readReg64 .x13 = ct1Cap)
    (hx14 : s.readReg64 .x14 = ct1Ptr) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_6904_to_ret_of_sub_placed (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
    hsp0_align hfsp_eq hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htr

theorem v9_tail_6904_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr) (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap) (hx13 : s.readReg64 .x13 = ct1Cap)
    (hx14 : s.readReg64 .x14 = ct1Ptr) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_6904_to_ret_of_dealloc_placed hA.dealloc
    st s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
    hsp0_align hfsp_eq hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htr

/-- From `+8588` (`drop_uc_8588`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_8588_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
        memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A.repAlloc (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
     ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
     A.pool lim st s ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize) by sep_ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
    ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
    vecCapPtrDealloc A.repAlloc rkCap rkPtr ∗ vecCapPtrDealloc A.repAlloc mkCap mkPtr ∗
    vecCapPtrDealloc A.repAlloc hdrCap hdrPtr ∗ vecCapPtrDealloc A.repAlloc esCap esPtr ∗
    vecCapPtrDealloc A.repAlloc ct1Cap ct1Ptr ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
     memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
     memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
  refine v9_seq_err_7084_evs_placed A lim st (F := F) s0 s fsp out pbA _ .stateDecode
    hsp0_align hfsp_eq
    (strengthen_evs_post ?_
      (v9_states_from_pb_drop_uc_8588_of_sub_placed hdealloc_ok st s0 s fsp out
        rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
         memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  intro evs sm
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 48 ∗ ((s0.sp - 2400#64 + 48#64) ↦₆₄ ct1Cap) ∗
     ((s0.sp - 2400#64 + 56#64) ↦₆₄ rkCap) ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
     ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗ memRegion (s0.sp - 2400#64 + 80#64) 48 ∗
     ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗ ((s0.sp - 2400#64 + 136#64) ↦₆₄ mkPtr) ∗
     ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗
     memRegion (s0.sp - 2400#64 + 160#64) 40 ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ct1Ptr) ∗
     memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ mkCap) ∗
     memRegion (s0.sp - 2400#64 + 224#64) 2080) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    A.pool lim (M.stepEvents evs st) sm ∗ memRegion pbA optProtoInnerStateSize by sep_ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_8588_entails_2304 (s0.sp - 2400#64)
      ct1Cap rkCap esPtr esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap))

theorem v9_tail_8588_to_ret_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
        memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_8588_to_ret_of_sub_placed (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    st s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
    hsp0_align hfsp_eq hpc hrun hsp hx19 hx28 htr

theorem v9_tail_8588_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
        memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_8588_to_ret_of_dealloc_placed hA.dealloc
    st s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
    hsp0_align hfsp_eq hpc hrun hsp hx19 hx28 htr

/-! ## 2. Post-`decoderFromPb` Tail (`+3044 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
/-- From `+3044` (after `decoderFromPb` returns) to `s0.x30` under explicit `subroutine_ok`
    contracts on `__rust_dealloc` and `memcpy`. -/
theorem v9_tail_3044_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (d : PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64) (hx25 : s.readReg64 .x25 = esLen)
    (hx26 : s.readReg64 .x26 = rkLen) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
        memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
        memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (∀ dec, decoderFromPbResult (pbToProtoPolyDecoder d) = .ok dec → evs = []) ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (match decoderFromPbResult (pbToProtoPolyDecoder d) with
               | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := (dec : spqrPolyApi.PolyDecoder) })
               | .error _ => .error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases decoderFromPbResult (pbToProtoPolyDecoder d) with
  | error err =>
    let FrameErr : SepProp :=
      ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
      ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
      ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
      ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
      ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
      ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
      memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
      memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
      memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
      memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
      v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
        esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
      memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
      FrameErr ∗ A.pool lim st s by dsimp only [FrameErr]; sep_ac_rfl)) ?_
    refine seq_clean_st (mid := lsmpl.base 333 + 8588#64)
      (P_mid := fun s1 => memRegion (fsp + 1888#64) 400 ∗ FrameErr ∗ A.pool lim st s1)
      (Q := fun s1 => VmPreserved s s1 ∧ s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0)
      (v9_step_3044_err_to_8588_placed_budget A lim st (ext := ext) s0 s fsp out rkPtr err
        FrameErr hfsp_align hpc hrun hsp hx19 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨_hvm1, hsp1, hx19_1, hx28_1, htr1⟩
    refine SepWP.weaken_pre ?_
      (SepWP.mono
        (v9_tail_8588_to_ret_of_sub_placed hdealloc_ok st s0 s1 fsp out pbA
          rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
          hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1)
        fun sf Pf _ _ ⟨evs, hevs, hPf, hrest⟩ =>
          ⟨evs, hevs, (fun _ h => nomatch h), hPf, hrest⟩)
    dsimp only [FrameErr]
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen)) ∗
       (((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 8 ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 28) ∗
       (memRegion (fsp + 224#64) 16 ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 641 ∗
        memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ∗
        memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16)) ∗
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
       ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
       ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
       memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
       v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
         esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s1 ∗ stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (v9_memRegion_3044_collapse_err fsp mkLen hdrLen
      (unshiftWord ct1Len (loByte uc.epoch)) uc.epoch
      ((loByte ct1Len).zeroExtend 32))) (Entails.of_eq (by sep_ac_rfl))
  | ok dec =>
    dsimp only [resultPolyDecoderFromPbAt]
    refine SepWP.weaken_pre (Entails.trans
      (sepConj_mono_left (v9_polyDecoderAt_relocate A.repAlloc (fsp + 1888#64) (out + 136#64) dec))
      (Entails.of_eq (show _ =
        (∃∗ bs : { l : List (BitVec 8) // l.length = 384 }, ∃∗ w392 : BitVec 64, ∃∗ P_heap : SepProp,
          ⌜(v9_wordAt bs.val 0).toNat < 2 ^ 63 ∧ loByte w392 = boolByte dec.isComplete ∧
            (((out + 136#64) ↦ₛ bs.val) ∗
             (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
             (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
               polyDecoderAt A.repAlloc (out + 136#64) dec)⌝ ∗
          ((fsp + 1888#64) ↦ₛ bs.val) ∗
          (((fsp + 1888#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((fsp + 1888#64) + 392#64) ↦₆₄ w392) ∗ P_heap) ∗
        (memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗
         memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641) ∗
        (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
         ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
         ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
         ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
         ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
           esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by sep_ac_rfl))) ?_
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (v9_memRegion_3044_split_ok fsp))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun w888 => ProofLib.SepWP.exists_left fun w880 =>
      ProofLib.SepWP.exists_left fun w864 => ProofLib.SepWP.exists_left fun q848 =>
      ProofLib.SepWP.exists_left fun w832 => ProofLib.SepWP.exists_left fun q816 =>
      ProofLib.SepWP.exists_left fun q800 => ProofLib.SepWP.exists_left fun q784 =>
      ProofLib.SepWP.exists_left fun q768 => ProofLib.SepWP.exists_left fun q752 =>
      ProofLib.SepWP.exists_left fun q736 => ProofLib.SepWP.exists_left fun q720 =>
      ProofLib.SepWP.exists_left fun q704 => ProofLib.SepWP.exists_left fun q688 =>
      ProofLib.SepWP.exists_left fun q672 => ProofLib.SepWP.exists_left fun q656 =>
      ProofLib.SepWP.exists_left fun q640 => ProofLib.SepWP.exists_left fun q624 =>
      ProofLib.SepWP.exists_left fun q608 => ProofLib.SepWP.exists_left fun w592 =>
      ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun w232 =>
      ProofLib.SepWP.exists_left fun w224 => ProofLib.SepWP.exists_left fun w208 =>
      ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
      ProofLib.SepWP.exists_left fun w160 => ProofLib.SepWP.exists_left fun w120 =>
      ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
      ProofLib.SepWP.exists_left fun d92 => ProofLib.SepWP.exists_left fun bs =>
      ProofLib.SepWP.exists_left fun w392 => ProofLib.SepWP.exists_left fun P_heap => ?_
    apply SepWP.pure_elim; rintro ⟨hw0_lt, _, hreloc⟩
    wp_conv_pre => rw [v9_bs384_eq_decCells bs.val bs.property (fsp + 1888#64)]
    let FrameOk : SepProp :=
      ((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
      memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 4 ∗
      memRegion (fsp + 100#64) 4 ∗ memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗
      memRegion (fsp + 255#64) 313 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗
      memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 1 ∗
      memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
      v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
        esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
      P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
      ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
      ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
      ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
      ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
      ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
      ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
      ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
      ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
      ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
      ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
      ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
      ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 w864) ∗
      ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ loBytes7 w888) ∗
      v9_decCellsAt (fsp + 1888#64) bs.val ∗
      ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 2280#64) ↦₆₄ w392) ∗
      FrameOk ∗ A.pool lim st s by dsimp only [FrameOk]; sep_ac_rfl)) ?_
    refine seq_clean_st (mid := lsmpl.base 333 + 8180#64)
      (v9_step_3044_ok_to_8180_placed_budget A lim st (ext := ext) s0 s fsp out
        rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
        esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
        w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888
        (BitVec.ofNat 64 dec.ptsNeeded) w392 d172
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 bs.val FrameOk
        hfsp_align hw0_lt hpc hrun hsp hx19 hx21 hx24 hx25 hx26 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨_hvm1, hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1,
      hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
      hx28_1, hx30_1, htr1⟩
    have hpre8180 :
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
        ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 120#64) ↦₆₄ w392) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
        ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
        ((fsp + 172#64) ↦₃₂ (loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
        ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 208#64) ↦₆₄ rkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗
        ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
        ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
        ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
        ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
        ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
        ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
        ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
        ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
        ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
        ((fsp + 864#64) ↦ₛ loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
        ((fsp + 880#64) ↦₆₄ unshiftWord ct1Len (loByte uc.epoch)) ∗
        ((fsp + 888#64) ↦ₛ loBytes7 (uc.epoch >>> 8)) ∗
        v9_decCellsAt (fsp + 1888#64) bs.val ∗
        ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 2280#64) ↦₆₄ w392) ∗ FrameOk ∗ A.pool lim st s1 ⊢
        (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
        (((fsp + 1888#64) ↦₁₂₈ (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)) ∗
         ((fsp + 1904#64) ↦₁₂₈ (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16)) ∗
         ((fsp + 1920#64) ↦₆₄ v9_wordAt bs.val 32) ∗ memRegion (fsp + 1928#64) 376) ∗
        (memRegion fsp 92 ∗ memRegion (fsp + 96#64) 8 ∗ memRegion (fsp + 128#64) 32 ∗
         memRegion (fsp + 200#64) 8 ∗ memRegion (fsp + 216#64) 8 ∗ memRegion (fsp + 895#64) 993) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ unshiftWord ct1Len (loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
           esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool lim st s1) := by
      dsimp only [FrameOk]
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 313) ∗
        (v9_decCellsAt (fsp + 1888#64) bs.val ∗
         ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
         ((fsp + 2280#64) ↦₆₄ w392) ∗ memRegion (fsp + 2288#64) 16) ∗
        ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 56#64) ↦₆₄ rkCap) ∗ memRegion (fsp + 64#64) 8 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
          ((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 4) ∗
         (((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 4) ∗
         (((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap)) ∗
         ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         (memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952)) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ unshiftWord ct1Len (loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
           esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim st s1) by sep_ac_rfl)) ?_
      exact sepConj_mono (v9_loBytes7_64_313_entails_bs328 fsp
        (unshiftWord ct1Len (loByte uc.epoch)) uc.epoch)
        (sepConj_mono (v9_fsp_1888_entails_epilogue fsp (BitVec.ofNat 64 dec.ptsNeeded) w392 bs.val bs.property)
          (sepConj_mono_left (v9_fsp_8180_gaps_collapse fsp mkLen ct1Cap rkCap esPtr hdrLen
            esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap ((loByte ct1Len).zeroExtend 32))))
    refine SepWP.weaken_pre hpre8180 ?_
    subst hfsp_eq; rw [sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro bs240
    have hep :=
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed
        A lim st hmemcpy_ok s0 s1 out
      d92 ((loByte (v9_wordAt bs.val 8)).zeroExtend 32)
      (v9_wordAt bs.val 376) (BitVec.ofNat 64 dec.ptsNeeded) w392
      (v9_wordAt bs.val 312) (v9_wordAt bs.val 360) rkPtr
      (v9_wordAt bs.val 344) (v9_wordAt bs.val 296) bs240.val bs240.property q576 w592
      (v9_quadAt bs.val 32) (v9_quadAt bs.val 48) (v9_quadAt bs.val 64) (v9_quadAt bs.val 80)
      (v9_quadAt bs.val 96) (v9_quadAt bs.val 112) (v9_quadAt bs.val 128) (v9_quadAt bs.val 144)
      (v9_quadAt bs.val 160) (v9_quadAt bs.val 176) (v9_quadAt bs.val 192) (v9_quadAt bs.val 208)
      (v9_quadAt bs.val 224) (v9_quadAt bs.val 240) (v9_wordAt bs.val 256)
      (v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24))
      (v9_wordAt bs.val 24 >>> 8) (unshiftWord ct1Len (loByte uc.epoch))
      (uc.epoch >>> 8) (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
      (v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
         esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       P_heap ∗ memRegion pbA optProtoInnerStateSize)
      hsp0_align hpc1 hrun1 hsp1 hx6_1 hx19_1 hx23_1 htr1
    rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
        hx3_1, hx27_32_1, hx27_1, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1,
        hx10_1, hx26_1, hx12_1, hx1_1, hx28_1, hx16_1] at hep
    refine SepWP.weaken_pre
      (by unfold epilogueStackSlots epilogueStackGaps; exact Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono hep ?_)
    rintro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f, _hvm_f⟩
    refine ⟨[], FreeOnlyEvs.nil, (fun _ _ => rfl), ?_, hsp_f, hcc_f, htr_f⟩
    rw [M.stepEvents_nil]
    refine Entails.trans hPf ?_
    have hb96 : (esLen.extractLsb' 0 32).setWidth 8 = esLen.extractLsb' 0 8 := by bv_kernel
    have hd97 : (esLen >>> 8).extractLsb' 0 32 = esLen.extractLsb' 8 32 := by bv_kernel
    have hh101 : (((esLen >>> 8) >>> 32).setWidth 32).setWidth 16 = esLen.extractLsb' 40 16 := by
      bv_kernel
    have hb103 : (((esLen >>> 8) >>> 48).setWidth 32).setWidth 8 = esLen.extractLsb' 56 8 := by
      bv_kernel
    have hb120 : ((loByte ct1Len).zeroExtend 32).setWidth 8 = loByte ct1Len :=
      v9_zext32_setWidth8 (loByte ct1Len)
    rw [hb96, hd97, hh101, hb103, hb120]
    have hreloc' :
        ((out + 136#64) ↦ₛ bs.val) ∗
          (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢
          polyDecoderAt A.repAlloc (out + 136#64) dec := by
      simpa only [v9_bv_add_add_lit, Nat.reduceAdd] using hreloc
    have hout := v9_epilogueOutFull_entails_ct1Acknowledged A.repAlloc (F := F) out
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc bs.val bs.property w392 dec P_heap hreloc'
      (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property
      (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hout)

theorem v9_tail_3044_to_ret_of_hooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym allocMemcpyVmSpec)
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (d : PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64) (hx25 : s.readReg64 .x25 = esLen)
    (hx26 : s.readReg64 .x26 = rkLen) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
        memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
        memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (∀ dec, decoderFromPbResult (pbToProtoPolyDecoder d) = .ok dec → evs = []) ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (match decoderFromPbResult (pbToProtoPolyDecoder d) with
               | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := (dec : spqrPolyApi.PolyDecoder) })
               | .error _ => .error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_3044_to_ret_of_sub_placed
    (v9_sub_ok_dealloc_of_dealloc_placed hdealloc)
    (spqr_hook_ok_of_mem hmemcpy)
    st s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc d
    hsp0_align hfsp_eq hpc hrun hsp hx19 hx21 hx24 hx25 hx26 hx28 htr

theorem v9_tail_3044_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (d : PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64) (hx25 : s.readReg64 .x25 = esLen)
    (hx26 : s.readReg64 .x26 = rkLen) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        ((fsp + 240#64) ↦ₛ loBytes7 (unshiftWord ct1Len (loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
        memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
        memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        v9_ct1SentHeap A.repAlloc rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (∀ dec, decoderFromPbResult (pbToProtoPolyDecoder d) = .ok dec → evs = []) ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (match decoderFromPbResult (pbToProtoPolyDecoder d) with
               | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := (dec : spqrPolyApi.PolyDecoder) })
               | .error _ => .error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v9_tail_3044_to_ret_of_hooks_placed hA.dealloc hA.memcpy
    st s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
    esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc d
    hsp0_align hfsp_eq hpc hrun hsp hx19 hx21 hx24 hx25 hx26 hx28 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudget
