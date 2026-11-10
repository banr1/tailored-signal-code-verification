/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5dPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5d
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 5 (`NoHeaderReceived`, `+1344`, Block `333`) — Part D

Budget-threaded relocatable error cleanup paths (`+6420`, `+1396`, `+6520 -> s0.x30`) under
`FreeOnlyEvs` and `Authenticator` key-buffer cloning (`+3744 -> +6064`) under `AuthFromPbEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5dPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder ProtoAuthenticator V1State pbToProtoPolyDecoder)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbOnPanic
   statesFromPbSavedCells statesFromPbStack v10_vecU8Payload_entails_vecCapPtrDealloc
   v5_memRegion_224_join_auth v5_memRegion_224_split_auth v5_vecU8Heap_dup_bounds
   v5a_Saved6428Preserved v5a_optProtoPolyDecoderHeap v5a_optProtoUcHeap
   v5a_stackAt_allocHook_to_encoderFromPbStack v5a_stackAt_encoderFromPbStack_to_allocHook
   v5a_vecU8Heap v5a_vecU8Heap_entails_dealloc v5b_memRegion_2304_join_224_232)
open CryptoVerification.SpqrV1.Unchunked (vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   fitsEvents_append rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authKeyCloneEvents fitsEvents_of_fitsEnv_authFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlacedBudget
  (v5a_states_from_pb_dealloc_none_proto_decoder_6420_placed_budget
   v5a_states_from_pb_dealloc_proto_decoder_6428_of_sub_placed
   v5a_states_from_pb_dealloc_some_proto_decoder_6420_of_sub_placed
   v5a_states_from_pb_err_6500_placed_budget
   v5a_sub_ok_dealloc_of_placedHooks v5a_sub_ok_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5bPlacedBudget
  (v5b_clone_macKey_5964_to_6020_of_placedHooks
   v5b_clone_rootKey_4276_to_5964_of_placedHooks
   v5b_dealloc_old_auth_6020_to_6064_of_sub_placed
   v5b_step_1396_auth_none_to_6428_placed_budget
   v5b_step_1396_auth_some_to_6428_of_sub_placed
   v5b_step_1396_uc_none_to_6428_placed_budget
   v5b_step_3744_to_4276_auth_some_placed_budget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5cPlacedBudget
  (v5c_dealloc_cloned_auth_6520_to_6500_of_sub_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-! ## 1. Error Paths from `+6420`, `+1396`, and `+6520` (`-> s0.x30`, `FreeOnlyEvs`) -/

/-- Budget-threaded `+6420 -> s0.x30` `StateDecode` error cleanup under an explicit
    Block-`333` `__rust_dealloc` subroutine contract (`FreeOnlyEvs`). -/
theorem v5_err_6420_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out w8 w16 w24 w40 : BitVec 64) (d32 d36 : BitVec 32)
    (receivingHdr : Option PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6420#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : v5a_Saved6428Preserved s0 s1 (s0.sp - 2400#64) out w16 w8 0#64)
    (hx28_1 : s1.readReg64 .x28 = w24) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoPolyDecoderHeap A.repAlloc (receivingHdr.map pbToProtoPolyDecoder)
          w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases receivingHdr with
  | none =>
    dsimp only [Option.map, v5a_optProtoPolyDecoderHeap]
    apply ProofLib.SepWP.pure_elim; intro hw8; subst hw8
    have h6500 := v5a_states_from_pb_dealloc_none_proto_decoder_6420_placed_budget A lim st
      (ext := ext) s0 s1 (s0.sp - 2400#64) out w16 0#64
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
      hpc1 hrun1 hpres1
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq h6500 ?_)
    rintro s2 P2 hpc2 hrun2 ⟨hP2, ⟨hsp2, hx19_2, _, _, hx27_2, htr2⟩, _, _⟩
    have hx27_byte : (s2.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx27_2]; rfl
    have herr := v5a_states_from_pb_err_6500_placed_budget A lim st (F := F) (ext := ext)
      s0 s2 out .stateDecode Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx27_byte htr2
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl)))
      (SepWP.mono herr fun sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩ => ?_)
    refine ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, ?_, hsp_f, hcc_f, htr_f⟩
    rw [M.stepEvents_nil]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
  | some decPb =>
    dsimp only [Option.map, v5a_optProtoPolyDecoderHeap, pbToProtoPolyDecoder,
      LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    rw [sepConj_assoc]
    apply ProofLib.SepWP.pure_elim
    rintro ⟨hw24, _, _, hpts_le, hpts_cap_lt, _, _⟩
    rw [hw24] at hx28_1
    have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
    have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    let Frame6420 : SepProp :=
      memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
    have h6500 := v5a_states_from_pb_dealloc_some_proto_decoder_6420_of_sub_placed hdealloc_ok
      st s0 s1 (s0.sp - 2400#64) out w16 w8 0#64 decPb.pts Frame6420
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx28_1
    change SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6500#64) s1
      ((if w8 = 0#64 then emp
        else A.live w16 (w8.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 w16 decPb.pts ∗
          memRegion (w16 + BitVec.ofNat 64 (decPb.pts.length * 24))
            ((w8.toNat - decPb.pts.length) * 24)) ∗
        A.pool lim st s1 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗ Frame6420) _ at h6500
    refine SepWP.weaken_pre
      (Entails.trans (sepConj_mono_right (sepConj_mono_left hst_split))
        (Entails.of_eq (by dsimp only [Frame6420]; sep_ac_rfl)))
      (SepWP.seq h6500 ?_)
    rintro s2 P2 hpc2 hrun2 ⟨evs, hevs, hP2, ⟨hsp2, hx19_2, _, _, hx27_2, htr2⟩, _⟩
    have hx27_byte : (s2.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx27_2]; rfl
    have herr := v5a_states_from_pb_err_6500_placed_budget A lim (M.stepEvents evs st)
      (F := F) (ext := ext) s0 s2 out .stateDecode Rest
      hsp0_align hpc2 hrun2 hsp2 hx19_2 hx27_byte htr2
    refine SepWP.weaken_pre ?_ (SepWP.mono herr ?_)
    · refine Entails.trans hP2 ?_
      dsimp only [Frame6420]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗
           memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
          (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ A.pool lim (M.stepEvents evs st) s2 ∗ Rest) by
            sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hst_join) (Entails.of_eq (by sep_ac_rfl)))
    · intro sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩
      exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f⟩

theorem v5_err_6420_to_ret_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out w8 w16 w24 w40 : BitVec 64) (d32 d36 : BitVec 32)
    (receivingHdr : Option PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6420#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : v5a_Saved6428Preserved s0 s1 (s0.sp - 2400#64) out w16 w8 0#64)
    (hx28_1 : s1.readReg64 .x28 = w24) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoPolyDecoderHeap A.repAlloc (receivingHdr.map pbToProtoPolyDecoder)
          w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v5_err_6420_to_ret_of_sub_placed (v5a_sub_ok_dealloc_of_placedHooks hA) st s0 s1
    out w8 w16 w24 w40 d32 d36 receivingHdr Rest hsp0_align hpc1 hrun1 hpres1 hx28_1

theorem v5_err_6420_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out w8 w16 w24 w40 : BitVec 64) (d32 d36 : BitVec 32)
    (receivingHdr : Option PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6420#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : v5a_Saved6428Preserved s0 s1 (s0.sp - 2400#64) out w16 w8 0#64)
    (hx28_1 : s1.readReg64 .x28 = w24) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoPolyDecoderHeap A.repAlloc (receivingHdr.map pbToProtoPolyDecoder)
          w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v5_err_6420_to_ret_of_sub_placed (v5a_sub_ok_dealloc_placed hA) st s0 s1
    out w8 w16 w24 w40 d32 d36 receivingHdr Rest hsp0_align hpc1 hrun1 hpres1 hx28_1

/-- Budget-threaded `+1396 -> +6428 -> +6500 -> s0.x30` `MsgDecode` error cleanup under an explicit
    Block-`333` `__rust_dealloc` subroutine contract (`FreeOnlyEvs`). -/
theorem v5_err_1396_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived)
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = w72) (hx22_1 : s1.readReg64 .x22 = w16)
    (hx23_1 : s1.readReg64 .x23 = w8) (hx24_1 : s1.readReg64 .x24 = w48)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = w24)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
        v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
          w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .msgDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  let P_after_uc (st' : M.σ) (sm : State) : SepProp :=
    v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
      w8 w16 w24 d32 d36 w40 ∗
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    A.pool lim st' sm ∗ Rest
  have h6428 : SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6428#64) s1
      (v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗ P_after_uc st s1)
      (fun sm Pm =>
        ∃ evs1 : List AllocEvent,
          FreeOnlyEvs evs1 ∧
          (Pm ⊢ P_after_uc (M.stepEvents evs1 st) sm) ∧
          v5a_Saved6428Preserved s0 sm (s0.sp - 2400#64) out w16 w8 2#64 ∧
          sm.readReg64 .x28 = w24) := by
    cases uc with
    | none =>
      dsimp only [v5a_optProtoUcHeap]
      apply ProofLib.SepWP.pure_elim; intro hw48; rw [hw48] at hx24_1
      have hstep := v5b_step_1396_uc_none_to_6428_placed_budget A lim st (ext := ext)
        s0 s1 (s0.sp - 2400#64) out w16 w8 w24
        (v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
           w8 w16 w24 d32 d36 w40 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
        hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [P_after_uc]; sep_ac_rfl))
        (SepWP.mono hstep fun sm Pm _ _ ⟨hPm, _, hpres, hx28_m⟩ => ?_)
      refine ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, ?_, hpres, hx28_m⟩
      rw [M.stepEvents_nil]
      exact Entails.trans hPm (Entails.of_eq (by dsimp only [P_after_uc]; sep_ac_rfl))
    | some ucVal =>
      rcases ucVal with ⟨ep, optAuth⟩
      cases optAuth with
      | none =>
        dsimp only [v5a_optProtoUcHeap]
        apply ProofLib.SepWP.pure_elim; rintro ⟨hw48, _⟩; rw [hw48] at hx24_1
        have hstep := v5b_step_1396_auth_none_to_6428_placed_budget A lim st (ext := ext)
          s0 s1 (s0.sp - 2400#64) out w16 w8 w24
          (v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
             w8 w16 w24 d32 d36 w40 ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest)
          hpc1 hrun1 hsp1 hx19_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1
        refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [P_after_uc]; sep_ac_rfl))
          (SepWP.mono hstep fun sm Pm _ _ ⟨hPm, _, hpres, hx28_m⟩ => ?_)
        refine ⟨[], LibsignalBinary.Heap.FreeOnlyEvs.nil, ?_, hpres, hx28_m⟩
        rw [M.stepEvents_nil]
        exact Entails.trans hPm (Entails.of_eq (by dsimp only [P_after_uc]; sep_ac_rfl))
      | some authPb =>
        dsimp only [v5a_optProtoUcHeap, P_after_uc]
        rw [sepConj_assoc]
        apply ProofLib.SepWP.pure_elim; intro _
        have hd1 := v5a_vecU8Heap_entails_dealloc A.repAlloc authPb.rootKey w48 w56 w64
        have hd2 := v5a_vecU8Heap_entails_dealloc A.repAlloc authPb.macKey w72 w80 w88
        have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
        have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ =
              v5a_vecU8Heap A.repAlloc authPb.rootKey w48 w56 w64 ∗
              v5a_vecU8Heap A.repAlloc authPb.macKey w72 w80 w88 ∗
              stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
              (v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
                 w8 w16 w24 d32 d36 w40 ∗
               memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
               memRegion out chunkedStatesSize ∗ A.pool lim st s1 ∗ Rest) by sep_ac_rfl))
            (sepConj_mono hd1 (sepConj_mono hd2 (sepConj_mono_left hst_split)))) ?_
        rw [sepConj_assoc]
        apply ProofLib.SepWP.pure_elim; rintro ⟨_, _, hw48_lt, _⟩
        refine SepWP.weaken_pre
          (Entails.of_eq (show _ =
            ⌜w88 = BitVec.ofNat 64 authPb.macKey.length ∧
              authPb.macKey.length ≤ w72.toNat ∧ w72.toNat < 2 ^ 63 ∧ w80 ≠ 0#64⌝ ∗
            (vecCapPtrDealloc A.repAlloc w48 w56 ∗ vecCapPtrDealloc A.repAlloc w72 w80 ∗
             A.pool lim st s1 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
             (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
              v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
                w8 w16 w24 d32 d36 w40 ∗
              memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
              memRegion out chunkedStatesSize ∗ Rest)) by sep_ac_rfl)) ?_
        apply ProofLib.SepWP.pure_elim; intro _
        have hstep := v5b_step_1396_auth_some_to_6428_of_sub_placed hdealloc_ok st s0 s1
          (s0.sp - 2400#64) out w16 w8 w24 w48 w56 w72 w80
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
             w8 w16 w24 d32 d36 w40 ∗
           memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗ Rest)
          hfsp_align hw48_lt hpc1 hrun1 hsp1
          hx10_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 htr1
        refine SepWP.mono hstep fun sm Pm _ _ ⟨evs1, hevs1, hPm, hpres, hx28_m, _⟩ => ?_
        refine ⟨evs1, hevs1, Entails.trans hPm ?_, hpres, hx28_m⟩
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt (s0.sp - 2400#64) allocHookStack ∗
             memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
            (v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
               w8 w16 w24 d32 d36 w40 ∗
             memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗ A.pool lim (M.stepEvents evs1 st) sm ∗ Rest) by
              sep_ac_rfl))
          (Entails.trans (sepConj_mono_left hst_join) (Entails.of_eq (by sep_ac_rfl)))
  refine SepWP.seq h6428 ?_
  rintro s2 P2 hpc2 hrun2 ⟨evs1, hevs1, hP2, hpres2, hx28_2⟩
  refine SepWP.weaken_pre hP2 ?_
  dsimp only [P_after_uc, v5a_optProtoPolyDecoderHeap, pbToProtoPolyDecoder,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim
  rintro ⟨hw24, _, _, hpts_le, hpts_cap_lt, _, _⟩
  rw [hw24] at hx28_2
  have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
  have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  let Frame6428 : SepProp :=
    memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 2304 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have h6500 := v5a_states_from_pb_dealloc_proto_decoder_6428_of_sub_placed hdealloc_ok
    (M.stepEvents evs1 st) s0 s2 (s0.sp - 2400#64) out w16 w8 2#64 decPb.pts Frame6428
    hfsp_align hpts_le hpts_cap_lt hpc2 hrun2 hpres2 hx28_2
  change SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 6500#64) s2
    ((if w8 = 0#64 then emp
      else A.live w16 (w8.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 w16 decPb.pts ∗
        memRegion (w16 + BitVec.ofNat 64 (decPb.pts.length * 24))
          ((w8.toNat - decPb.pts.length) * 24)) ∗
      A.pool lim (M.stepEvents evs1 st) s2 ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗ Frame6428) _ at h6500
  refine SepWP.weaken_pre
    (Entails.trans (sepConj_mono_right (sepConj_mono_left hst_split))
      (Entails.of_eq (by dsimp only [Frame6428]; sep_ac_rfl)))
    (SepWP.seq h6500 ?_)
  rintro s3 P3 hpc3 hrun3 ⟨evs2, hevs2, hP3, ⟨hsp3, hx19_3, _, _, hx27_3, htr3⟩, _⟩
  have hx27_byte : (s3.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .msgDecode := by
    rw [hx27_3]; rfl
  have herr := v5a_states_from_pb_err_6500_placed_budget A lim (M.stepEvents (evs1 ++ evs2) st)
    (F := F) (ext := ext) s0 s3 out .msgDecode Rest
    hsp0_align hpc3 hrun3 hsp3 hx19_3 hx27_byte htr3
  refine SepWP.weaken_pre ?_ (SepWP.mono herr ?_)
  · rw [← M.stepEvents_append] at hP3
    refine Entails.trans hP3 ?_
    dsimp only [Frame6428]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗
         memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents (evs1 ++ evs2) st) s3 ∗ Rest) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hst_join) (Entails.of_eq (by sep_ac_rfl)))
  · intro sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩
    exact ⟨evs1 ++ evs2, hevs1.append hevs2,
      Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f⟩

theorem v5_err_1396_to_ret_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived)
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = w72) (hx22_1 : s1.readReg64 .x22 = w16)
    (hx23_1 : s1.readReg64 .x23 = w8) (hx24_1 : s1.readReg64 .x24 = w48)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = w24)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
        v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
          w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .msgDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v5_err_1396_to_ret_of_sub_placed (v5a_sub_ok_dealloc_of_placedHooks hA) st s0 s1
    out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36 uc decPb Rest
    hsp0_align hpc1 hrun1 hsp1 hx10_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 htr1

theorem v5_err_1396_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 : BitVec 64)
    (d32 d36 : BitVec 32)
    (uc : Option V1State.Unchunked.NoHeaderReceived)
    (decPb : PolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = w72) (hx22_1 : s1.readReg64 .x22 = w16)
    (hx23_1 : s1.readReg64 .x23 = w8) (hx24_1 : s1.readReg64 .x24 = w48)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = w24)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (v5a_optProtoUcHeap A.repAlloc uc w48 w56 w64 w72 w80 w88 w96 ∗
        v5a_optProtoPolyDecoderHeap A.repAlloc (some (pbToProtoPolyDecoder decPb))
          w8 w16 w24 d32 d36 w40 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .msgDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v5_err_1396_to_ret_of_sub_placed (v5a_sub_ok_dealloc_placed hA) st s0 s1
    out w8 w16 w24 w40 w48 w56 w64 w72 w80 w88 w96 d32 d36 uc decPb Rest
    hsp0_align hpc1 hrun1 hsp1 hx10_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 htr1

/-- Budget-threaded `+6520 -> +6500 -> s0.x30` `StateDecode` error cleanup of cloned
    `rootKey` and `macKey` buffers under an explicit Block-`333` `__rust_dealloc` contract
    (`FreeOnlyEvs`). -/
theorem v5_err_6520_to_ret_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s1 : State) (out p1_new p2_new l1 l2 ep w200 w224 : BitVec 64) (d232 : BitVec 32)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6520#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = l1)
    (hx27_1 : s1.readReg64 .x27 = p1_new) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
        memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗ vecU8Payload A.repAlloc l2 p2_new macKey ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hd1 := v10_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc l1 p1_new rootKey
  have hd2 := v10_vecU8Payload_entails_vecCapPtrDealloc A.repAlloc l2 p2_new macKey
  have hst_split := v5a_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
  have hst_join := v5a_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
  let R_stack : SepProp :=
    memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
    memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
    (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
    (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
    (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
    memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have h6500 := v5c_dealloc_cloned_auth_6520_to_6500_of_sub_placed hdealloc_ok st s0 s1
    (s0.sp - 2400#64) out p1_new p2_new l1 l2 R_stack
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx27_1 htr1
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗ vecU8Payload A.repAlloc l2 p2_new macKey ∗
        ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
         A.pool lim st s1 ∗ memRegion (s0.sp - 2400#64) 136 ∗
         memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
         (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) by sep_ac_rfl))
      (Entails.trans (sepConj_mono hst_split (sepConj_mono hd1 (sepConj_mono_left hd2)))
        (Entails.of_eq (by dsimp only [R_stack]; sep_ac_rfl))))
    (SepWP.seq h6500 ?_)
  rintro s2 P2 hpc2 hrun2 ⟨evs, hevs, hP2, hsp2, hx19_2, hx27_2, htr2, _⟩
  have h224 := v5_memRegion_224_join_auth (s0.sp - 2400#64) p2_new ep w200 p1_new l2
  have h2304 := v5b_memRegion_2304_join_224_232 (s0.sp - 2400#64) w224 d232
  have hx27_byte : (s2.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx27_2]; rfl
  have herr := v5a_states_from_pb_err_6500_placed_budget A lim (M.stepEvents evs st)
    (F := F) (ext := ext) s0 s2 out .stateDecode Rest
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx27_byte htr2
  refine SepWP.weaken_pre ?_ (SepWP.mono herr ?_)
  · refine Entails.trans hP2 ?_
    dsimp only [R_stack]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗
         memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        ((memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
          memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
          memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗
          (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2)) ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
         memRegion ((s0.sp - 2400#64) + 236#64) 2068) ∗
        (statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         A.pool lim (M.stepEvents evs st) s2 ∗ Rest) by sep_ac_rfl))
      (Entails.trans
        (sepConj_mono hst_join (sepConj_mono_left (Entails.trans (sepConj_mono_left h224) h2304)))
        (Entails.of_eq (by sep_ac_rfl)))
  · intro sf Pf _ _ ⟨hPf, _, hsp_f, hcc_f, htr_f⟩
    exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f⟩

theorem v5_err_6520_to_ret_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1_new p2_new l1 l2 ep w200 w224 : BitVec 64) (d232 : BitVec 32)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6520#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = l1)
    (hx27_1 : s1.readReg64 .x27 = p1_new) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
        memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗ vecU8Payload A.repAlloc l2 p2_new macKey ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v5_err_6520_to_ret_of_sub_placed (v5a_sub_ok_dealloc_of_placedHooks hA) st s0 s1
    out p1_new p2_new l1 l2 ep w200 w224 d232 rootKey macKey Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx27_1 htr1

theorem v5_err_6520_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State) (out p1_new p2_new l1 l2 ep w200 w224 : BitVec 64) (d232 : BitVec 32)
    (rootKey macKey : List (BitVec 8)) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6520#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx21_1 : s1.readReg64 .x21 = l1)
    (hx27_1 : s1.readReg64 .x27 = p1_new) (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
        memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w200) ∗
        (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ l2) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w224) ∗ (((s0.sp - 2400#64) + 232#64) ↦₃₂ d232) ∗
        memRegion ((s0.sp - 2400#64) + 236#64) 2068 ∗
        vecU8Payload A.repAlloc l1 p1_new rootKey ∗ vecU8Payload A.repAlloc l2 p2_new macKey ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        A.pool lim st s1 ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) :=
  v5_err_6520_to_ret_of_sub_placed (v5a_sub_ok_dealloc_placed hA) st s0 s1
    out p1_new p2_new l1 l2 ep w200 w224 d232 rootKey macKey Rest
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx27_1 htr1

/-! ## 2. Budget-Threaded `Authenticator` Cloning (`+3744 -> +6064`) -/

/-- Clones `authPb.rootKey` and `authPb.macKey` and frees the original `ProtoAuthenticator`
    buffers at `+3744 -> +4276 -> +5964 -> +6020 -> +6064` under
    `FitsEvents M lim st (authFromPbEvents authPb)` without panic or OOM. -/
theorem v5_auth_some_3744_to_6064_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep : BitVec 64)
    (authPb : ProtoAuthenticator) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authFromPbEvents authPb))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6064#64) s1
      (v5a_optProtoUcHeap A.repAlloc (some { auth := some authPb, epoch := ep })
          w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 224 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs_free : List AllocEvent) (p1_new p2_new : BitVec 64),
          FreeOnlyEvs evs_free ∧
          authPb.rootKey.length < 2 ^ 63 ∧ authPb.macKey.length < 2 ^ 63 ∧
          (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
            memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
            memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
            A.pool lim (M.stepEvents (authFromPbEvents authPb ++ evs_free) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x27 = p1_new ∧
          sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  obtain ⟨hfit_r, hfit_m⟩ :=
    (fitsEvents_append M lim (authKeyCloneEvents authPb.rootKey)
      (authKeyCloneEvents authPb.macKey) st).mp hfits
  dsimp only [v5a_optProtoUcHeap]
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        ⌜w96 = ep⌝ ∗ v5a_vecU8Heap A.repAlloc authPb.rootKey w48 w56 w64 ∗
        v5a_vecU8Heap A.repAlloc authPb.macKey w72 w80 w88 ∗ memRegion (s0.sp - 2400#64) 224 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool lim st s1 ∗ Rest) by sep_ac_rfl))
      (sepConj_mono_right
        (sepConj_mono (v5_vecU8Heap_dup_bounds A.repAlloc authPb.rootKey w48 w56 w64)
          (sepConj_mono (v5_vecU8Heap_dup_bounds A.repAlloc authPb.macKey w72 w80 w88)
            (sepConj_mono_left (v5_memRegion_224_split_auth (s0.sp - 2400#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun z216 => ProofLib.SepWP.exists_left fun z208 =>
    ProofLib.SepWP.exists_left fun z200 => ProofLib.SepWP.exists_left fun z152 =>
    ProofLib.SepWP.exists_left fun z136 => ?_
  apply ProofLib.SepWP.pure_elim; intro hw96
  apply ProofLib.SepWP.pure_elim; rintro ⟨hw64, hr_lt63, hw48_lt⟩
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      ⌜w88 = BitVec.ofNat 64 authPb.macKey.length ∧
        authPb.macKey.length < 2 ^ 63 ∧ w72.toNat < 2 ^ 63⌝ ∗
      ((((s0.sp - 2400#64) + 152#64) ↦₆₄ z152) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ z200) ∗
       (((s0.sp - 2400#64) + 216#64) ↦₆₄ z216) ∗ A.pool lim st s1 ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ z208) ∗
        vecU8Payload A.repAlloc w48 w56 authPb.rootKey ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗
        vecU8Payload A.repAlloc w72 w80 authPb.macKey ∗ memRegion (s0.sp - 2400#64) 136 ∗
        memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗
        Rest)) by sep_ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; rintro ⟨hw88, hm_lt63, _⟩
  have hl1_lt : (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hr_lt63
  rw [hw96] at hx9_1; rw [hw64] at hx20_1; rw [hw88] at hx8_1
  have h4276 := v5b_step_3744_to_4276_auth_some_placed_budget A lim st (ext := ext) s0 s1
    (s0.sp - 2400#64) out (BitVec.ofNat 64 authPb.macKey.length) ep w80
    (BitVec.ofNat 64 authPb.rootKey.length) w72 ptsPtr ptsCap w48 d32_64 w56 ptsLen
    z152 z200 z216
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ z208) ∗
     vecU8Payload A.repAlloc w48 w56 authPb.rootKey ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗
     vecU8Payload A.repAlloc w72 w80 authPb.macKey ∗ memRegion (s0.sp - 2400#64) 136 ∗
     memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest)
    hfsp_align hw48_lt hpc1 hrun1 hsp1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1
    hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1
  refine SepWP.seq h4276 ?_
  rintro s2 P2 hpc2 hrun2
    ⟨hP2, _, hsp2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
  have h5964 := v5b_clone_rootKey_4276_to_5964_of_placedHooks hA st s0 s2
    out w56 w48 w72 (BitVec.ofNat 64 authPb.macKey.length) ptsPtr ptsCap ptsLen d32_64 z208
    authPb.rootKey
    ((((s0.sp - 2400#64) + 136#64) ↦₆₄ z136) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗ vecU8Payload A.repAlloc w72 w80 authPb.macKey ∗
     memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest)
    hfit_r hsp0_align hpc2 hrun2 hsp2
    hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl))) (SepWP.seq h5964 ?_)
  rintro s3 P3 hpc3 hrun3
    ⟨p1_new, hP3, hsp3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx28_3, htr3⟩
  let st_r := M.stepEvents (authKeyCloneEvents authPb.rootKey) st
  have h6020 := v5b_clone_macKey_5964_to_6020_of_placedHooks hA st_r s0 s3
    out w56 w80 w48 w72 (BitVec.ofNat 64 authPb.rootKey.length) ptsPtr ptsCap ptsLen d32_64 z136
    authPb.macKey
    ((((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
     (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
     vecCapPtrDealloc A.repAlloc w48 w56 ∗ memRegion (s0.sp - 2400#64) 136 ∗
     memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest)
    hfit_m hsp0_align hpc3 hrun3 hsp3
    hx8_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 htr3
  refine SepWP.weaken_pre (Entails.trans hP3 (Entails.of_eq (by dsimp only [st_r]; sep_ac_rfl)))
    (SepWP.seq h6020 ?_)
  rintro s4 P4 hpc4 hrun4
    ⟨p2_new, hP4, hsp4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx28_4, htr4⟩
  have hst_auth : M.stepEvents (authKeyCloneEvents authPb.macKey) st_r =
      M.stepEvents (authFromPbEvents authPb) st := by
    dsimp only [st_r, authFromPbEvents]; rw [M.stepEvents_append]
  have h6064 := v5b_dealloc_old_auth_6020_to_6064_of_sub_placed
    (v5a_sub_ok_dealloc_of_placedHooks hA) (M.stepEvents (authFromPbEvents authPb) st) s0 s4
    out w56 w80 p1_new w48 w72 (BitVec.ofNat 64 authPb.rootKey.length) ptsPtr ptsCap ptsLen d32_64
    ((((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
     (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
     vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
     memRegion (s0.sp - 2400#64) 136 ∗ memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ Rest)
    hsp0_align hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx28_4 htr4
  refine SepWP.weaken_pre
    (Entails.trans hP4 (Entails.of_eq (by rw [hst_auth]; sep_ac_rfl)))
    (SepWP.mono h6064 ?_)
  rintro sm Pm _ _
    ⟨evs_free, hfree, hPm, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m, hx25_m, hx27_m, hx28_m, htr_m, _⟩
  refine ⟨evs_free, p1_new, p2_new, hfree, hr_lt63, hm_lt63, hl1_lt, ?_,
    hsp_m, hx19_m, hx20_m, hx22_m, hx23_m, hx25_m, hx27_m, hx28_m, htr_m⟩
  rw [M.stepEvents_append]
  exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))

theorem v5_auth_some_3744_to_6064_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep : BitVec 64)
    (authPb : ProtoAuthenticator) (Rest : SepProp)
    (hfits : FitsEvents M lim st (authFromPbEvents authPb))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6064#64) s1
      (v5a_optProtoUcHeap A.repAlloc (some { auth := some authPb, epoch := ep })
          w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 224 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs_free : List AllocEvent) (p1_new p2_new : BitVec 64),
          FreeOnlyEvs evs_free ∧
          authPb.rootKey.length < 2 ^ 63 ∧ authPb.macKey.length < 2 ^ 63 ∧
          (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
            memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
            memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
            A.pool lim (M.stepEvents (authFromPbEvents authPb ++ evs_free) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x27 = p1_new ∧
          sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0) :=
  v5_auth_some_3744_to_6064_of_placedHooks hA.toPlacedBudget st s0 s1
    out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep authPb Rest
    hfits hsp0_align hpc1 hrun1 hsp1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1
    hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1

theorem v5_auth_some_3744_to_6064_of_env_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep : BitVec 64)
    (authPb : ProtoAuthenticator) (Rest : SepProp)
    (hfits : FitsEnv M lim st (AuthFromPbEnv authPb))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6064#64) s1
      (v5a_optProtoUcHeap A.repAlloc (some { auth := some authPb, epoch := ep })
          w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 224 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs_free : List AllocEvent) (p1_new p2_new : BitVec 64),
          FreeOnlyEvs evs_free ∧
          authPb.rootKey.length < 2 ^ 63 ∧ authPb.macKey.length < 2 ^ 63 ∧
          (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
            memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
            memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
            A.pool lim (M.stepEvents (authFromPbEvents authPb ++ evs_free) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x27 = p1_new ∧
          sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0) :=
  v5_auth_some_3744_to_6064_of_placedHooks hA st s0 s1
    out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep authPb Rest
    (fitsEvents_of_fitsEnv_authFromPbEnv hfits) hsp0_align hpc1 hrun1 hsp1
    hx8_1 hx9_1 hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1

theorem v5_auth_some_3744_to_6064_wpp_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (st : M.σ) (s0 s1 : State)
    (out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep : BitVec 64)
    (authPb : ProtoAuthenticator) (Rest R : SepProp)
    (hfits : FitsEvents M lim st (authFromPbEvents authPb))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3744#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = w88) (hx9_1 : s1.readReg64 .x9 = w96)
    (hx10_1 : s1.readReg64 .x10 = w80) (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = w64) (hx21_1 : s1.readReg64 .x21 = w72)
    (hx22_1 : s1.readReg64 .x22 = ptsPtr) (hx23_1 : s1.readReg64 .x23 = ptsCap)
    (hx24_1 : s1.readReg64 .x24 = w48) (hx25_1 : s1.readReg64 .x25 = d32_64)
    (hx26_1 : s1.readReg64 .x26 = w56) (hx28_1 : s1.readReg64 .x28 = ptsLen)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6064#64) s1
      (v5a_optProtoUcHeap A.repAlloc (some { auth := some authPb, epoch := ep })
          w48 w56 w64 w72 w80 w88 w96 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 224 ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ (evs_free : List AllocEvent) (p1_new p2_new : BitVec 64),
          FreeOnlyEvs evs_free ∧
          authPb.rootKey.length < 2 ^ 63 ∧ authPb.macKey.length < 2 ^ 63 ∧
          (BitVec.ofNat 64 authPb.rootKey.length).toNat < 2 ^ 63 ∧
          (Pm ⊢
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            memRegion (s0.sp - 2400#64) 136 ∗ (((s0.sp - 2400#64) + 136#64) ↦₆₄ p2_new) ∗
            memRegion ((s0.sp - 2400#64) + 144#64) 8 ∗ (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
            memRegion ((s0.sp - 2400#64) + 160#64) 40 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ w80) ∗
            (((s0.sp - 2400#64) + 208#64) ↦₆₄ p1_new) ∗
            (((s0.sp - 2400#64) + 216#64) ↦₆₄ BitVec.ofNat 64 authPb.macKey.length) ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.rootKey.length) p1_new authPb.rootKey ∗
            vecU8Payload A.repAlloc (BitVec.ofNat 64 authPb.macKey.length) p2_new authPb.macKey ∗
            A.pool lim (M.stepEvents (authFromPbEvents authPb ++ evs_free) st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 authPb.rootKey.length ∧
          sm.readReg64 .x22 = ptsPtr ∧ sm.readReg64 .x23 = ptsCap ∧
          sm.readReg64 .x25 = d32_64 ∧ sm.readReg64 .x27 = p1_new ∧
          sm.readReg64 .x28 = ptsLen ∧ TraceCalleeSaved sm s0)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP_ret (v5_auth_some_3744_to_6064_of_placedHooks hA st s0 s1
    out ptsPtr ptsCap ptsLen d32_64 w48 w56 w64 w72 w80 w88 w96 ep authPb Rest
    hfits hsp0_align hpc1 hrun1 hsp1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1
    hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 htr1)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5dPlacedBudget
