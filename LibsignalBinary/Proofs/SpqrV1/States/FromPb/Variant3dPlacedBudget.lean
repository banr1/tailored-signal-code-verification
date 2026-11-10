/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 3 (`Ct1Received`) — Post-`uc` Composition

Relocatable Block-`333` post-encoder and `sendingEk = some pbEnc` continuations (`+924`,
`+1012`, `+1024 -> ret`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_333 blkPl_333
   lsProg_333 lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder ProtoPolynomialEncoder States V1State pbToProtoPolyEncoder
   spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize
   resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack fromPbResult)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte
   statesFromPbJumpTablePlacedAt statesFromPbOnPanic
   statesFromPbSavedCells statesFromPbStack
   v1_bv_add_add_lit v1_optProtoPolyEncoderAt_pack_some
   v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt v1_ucWordsAt
   v10_resultPolyEncoder_err_entails_tag_392
   v3_collapse_1888_400 v3_collapse_fsp_232_1656
   v3_collapse_fsp_296_1592 v3_collapse_pbA_112_224
   v3cr_polyEncoderAt_open v3cr_polyEncoderHeap v3cr_polyEncoderWordsAt
   v3cr_states_from_pb_ct1Received_ok_eq
   v3cr_states_from_pb_ct1Received_sendingEk_err_any_eq
   v3cr_unchunkedEkSentCt1ReceivedHeap v3cr_unchunkedHeap_entails_dealloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbSpec
   fitsEnv_encoderFromPbAllocEnv_of_encoderFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget
   encoder_from_pb_ok_of_alloc_placed seq_clean_lscl_st
   v1_dealloc_ok_at_statesFromPb_placed v1_dealloc_ok_of_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
  (v3cr_states_from_pb_err_1024_of_sub_placed
   v3cr_states_from_pb_err_4968_placed_budget)

export Variant3dPlacedBudgetAux
  (v3cr_copy_enc_to_call_924_placed v3cr_copy_enc_to_call_924_placed_budget
   v3cr_post_enc_1012_err_placed v3cr_post_enc_1012_err_placed_budget
   v3cr_post_enc_1012_ok_placed v3cr_post_enc_1012_ok_placed_budget)
export Variant3dPlacedBudgetAux
  (v3cr_pack_enc_4984_to_8180_placed v3cr_pack_enc_4984_to_8180_placed_budget
   v3_ct1Received_ok_4984_to_exit_of_memcpy_placed
   v3_ct1Received_ok_4984_to_exit_placed
   v3_ct1Received_err_4884_to_exit_of_sub_placed
   v3_ct1Received_err_4884_to_exit_of_dealloc_placed
   v3_ct1Received_err_4884_to_exit_placed)

alias v3_sepWPp_seq_clean_lscl :=
  _root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3_sepWPp_seq_clean_lscl
alias v3_sepWPp_call_lscl :=
  _root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3_sepWPp_call_lscl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-! ## Budget-Threaded `Err(Error::StateDecode)` 4-Vector Dealloc Exits (`+1024`, `+4884`) -/

private theorem memRegion_2304_of_1024 (fsp uc_ep la3 pa3 pa2 la4 ca1 ca4 : BitVec 64) :
    memRegion fsp 64 ∗
      ((fsp + 64#64) ↦₆₄ uc_ep) ∗
      memRegion (fsp + 72#64) 24 ∗
      ((fsp + 96#64) ↦₆₄ la3) ∗
      memRegion (fsp + 104#64) 72 ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 192#64) ↦₆₄ la4) ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      memRegion (fsp + 208#64) 16 ∗
      ((fsp + 224#64) ↦₆₄ ca4) ∗
      memRegion (fsp + 232#64) 2072 ⊢
    memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 64) (k := 2240) (b' := fsp + 64#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 64#64) (n := 8) (k := 2232) (b' := fsp + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 72#64) (n := 24) (k := 2208) (b' := fsp + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 96#64) (n := 8) (k := 2200) (b' := fsp + 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 104#64) (n := 72) (k := 2128) (b' := fsp + 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 8) (k := 2120) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 8) (k := 2112) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 2104) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 8) (k := 2096) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 16) (k := 2080) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 8) (k := 2072) (b' := fsp + 232#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (Entails.refl _)
                      (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))))))))

/-- Budget-threaded `+1024 -> +4968 -> s0.x30` 4-vector dealloc error exit under an explicit
    Block-`333` `__rust_dealloc` contract, emitting `FreeOnlyEvs`. -/
theorem v3_ct1Received_err_1024_to_exit_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1024#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = pa1)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt s0.sp statesFromPbStack ∗ Rest) ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have h1024 := Variant3bPlacedBudget.v3cr_states_from_pb_err_1024_of_sub_placed hdealloc_ok st s0 s out
    ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4
    (memRegion (s0.sp - 2400#64) 64 ∗
     (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
     memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
     (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
     memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
     (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
     memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ Rest)
    hsp0_align hpc hrun hsp hx19 hx22 hx28 hx26 hx21 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) h1024) ?_
  rintro s2 P2 hpc2 hrun2 ⟨evs, hevs, hP2, hsp2, hx19_2, hx22_2, htr2⟩
  have h2304 := memRegion_2304_of_1024 (s0.sp - 2400#64) uc_ep la3 pa3 pa2 la4 ca1 ca4
  have hP2' : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs st) s2 ∗
      (memRegion pbA optProtoInnerStateSize ∗ Rest) := by
    refine Entails.trans hP2 ?_
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (memRegion (s0.sp - 2400#64) 64 ∗
       (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
       (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       memRegion ((s0.sp - 2400#64) + 232#64) 2072) ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs st) s2 ∗
      (memRegion pbA optProtoInnerStateSize ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left h2304)
  have hx22_byte : (s2.readReg64 .x22).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
    rw [hx22_2]; rfl
  have h4968 := v3cr_states_from_pb_err_4968_placed_budget A lim (M.stepEvents evs st)
    (F := F) (ext := ext) s0 s2 out .stateDecode
    (memRegion pbA optProtoInnerStateSize ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_byte htr2
  refine SepWP.weaken_pre hP2' (SepWP.mono h4968 ?_)
  intro sm Pm _ _ ⟨hPm, _hvm, hsp_m, hcc_m, htr_m⟩
  exact ⟨evs, hevs, Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp_m, hcc_m, htr_m⟩

theorem v3_ct1Received_err_1024_to_exit_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1024#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = pa1)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt s0.sp statesFromPbStack ∗ Rest) ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) :=
  v3_ct1Received_err_1024_to_exit_of_sub_placed
    (Variant2aPlacedBudget.v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s out pbA ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep Rest
    hsp0_align hpc hrun hsp hx19 hx22 hx28 hx26 hx21 htr

/-- Budget-threaded `+1024 -> +4968 -> s0.x30` 4-vector dealloc error exit under
    `FromPbAllocHooksBudget M A lim ext`. -/
theorem v3_ct1Received_err_1024_to_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1024#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = pa1)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt s0.sp statesFromPbStack ∗ Rest) ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) :=
  v3_ct1Received_err_1024_to_exit_of_dealloc_placed hA.dealloc st s0 s out pbA
    ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep Rest
    hsp0_align hpc hrun hsp hx19 hx22 hx28 hx26 hx21 htr

/-! ## Budget-Threaded Post-`PolyEncoder::from_pb` Continuation (`+1012 -> s0.x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded post-`<PolyEncoder>::from_pb` continuation at `+1012` (`+1012 -> s0.x30`,
    Block `333`) under explicit `__rust_dealloc` and `memcpy` contracts, emitting `FreeOnlyEvs`. -/
theorem v3_ct1Received_post_enc_1012_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (Rest : SepProp)
    (huc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1012#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = la2)
    (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = ca2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
          (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt s0.sp statesFromPbStack ∗ Rest) ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  cases henc : fromPbResult (pbToProtoPolyEncoder pbEnc) with
  | error err =>
    rw [v3cr_states_from_pb_ct1Received_sendingEk_err_any_eq u ucSt pbEnc err huc henc]
    have herr := v10_resultPolyEncoder_err_entails_tag_392 A.repAlloc (s0.sp - 2400#64) err
    have hdealloc := v3cr_unchunkedHeap_entails_dealloc A.repAlloc (F := F) ucSt
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    have hpre_err :
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest ⊢
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        A.pool lim st s ∗
        (memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗
         (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
         (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
         memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
         vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ Rest) := by
      refine Entails.trans (Entails.of_eq (show _ =
        resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        (A.pool lim st s ∗
         memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗
         (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
         (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
         memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono herr (sepConj_mono_left hdealloc)) (Entails.of_eq (by ac_rfl))
    refine SepWP.seq (SepWP.weaken_pre hpre_err
      (v3cr_post_enc_1012_err_placed_budget A lim st (ext := ext) s (s0.sp - 2400#64) out pa1 pa4 ca3 ca2 _
        hfsp_align hpc hrun hsp hx19 hx21 hx22 hx26 hx28)) ?_
    intro s2 P2 hpc2 hrun2 ⟨hP2, _hvm2, hsp2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
    have h2072 :
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ⊢
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 := by
      rw [ProofLib.memRegion_split' (b := (s0.sp - 2400#64) + 232#64) (n := 1656) (k := 416)
            (b' := (s0.sp - 2400#64) + 1888#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := (s0.sp - 2400#64) + 1888#64) (n := 8) (k := 408)
            (b' := (s0.sp - 2400#64) + 1896#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := (s0.sp - 2400#64) + 1896#64) (n := 392) (k := 16)
            (b' := (s0.sp - 2400#64) + 2288#64) rfl (by bv_omega) (by decide)]
      refine Entails.trans (Entails.of_eq (show _ =
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
        memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 by ac_rfl)) ?_
      exact sepConj_mono (Entails.refl _)
        (sepConj_mono_left (pointsTo64_entails_memRegion _ _))
    have hP2' : P2 ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s2 ∗ Rest := by
      refine Entails.trans hP2 ?_
      refine Entails.trans (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
         memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 64 ∗
         (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
         memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
         (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
         memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
         (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
         (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
         (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
         vecCapPtrDealloc A.repAlloc ca1 pa1 ∗ vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
         vecCapPtrDealloc A.repAlloc ca3 pa3 ∗ vecCapPtrDealloc A.repAlloc ca4 pa4 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s2 ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h2072) (Entails.of_eq (by ac_rfl))
    exact SepWP.weaken_pre hP2'
      (v3_ct1Received_err_1024_to_exit_of_sub_placed hdealloc_ok st s0 s2 out pbA
        ca1 pa1 ca2 pa2 ca3 pa3 la3 ca4 pa4 la4 uc_ep Rest
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx28_2 hx26_2 hx21_2 (htr2.trans htr))
  | ok enc =>
    rw [v3cr_states_from_pb_ct1Received_ok_eq u ucSt pbEnc enc huc henc]
    dsimp only [resultPolyEncoderFromPbAt]
    have hopen := v3cr_polyEncoderAt_open A.repAlloc ((s0.sp - 2400#64) + 1888#64) enc
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hopen)))))))))))))) ?_
    wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w_tag
    apply ProofLib.SepWP.exists_left; intro e_w8; apply ProofLib.SepWP.exists_left; intro e_w16
    apply ProofLib.SepWP.exists_left; intro e_w24; apply ProofLib.SepWP.exists_left; intro e_w32
    apply ProofLib.SepWP.exists_left; intro e_w40; apply ProofLib.SepWP.exists_left; intro e_w48
    apply ProofLib.SepWP.exists_left; intro e_w56; apply ProofLib.SepWP.exists_left; intro e_w64
    apply ProofLib.SepWP.exists_left; intro e_w72; apply ProofLib.SepWP.exists_left; intro e_w80
    apply ProofLib.SepWP.exists_left; intro e_w88; apply ProofLib.SepWP.exists_left; intro e_w96
    apply ProofLib.SepWP.exists_left; intro e_w104; apply ProofLib.SepWP.exists_left; intro e_w112
    apply ProofLib.SepWP.exists_left; intro e_w120; apply ProofLib.SepWP.exists_left; intro e_w128
    apply ProofLib.SepWP.exists_left; intro e_w136; apply ProofLib.SepWP.exists_left; intro e_w144
    apply ProofLib.SepWP.exists_left; intro e_w152; apply ProofLib.SepWP.exists_left; intro e_q160
    apply ProofLib.SepWP.exists_left; intro e_q176; apply ProofLib.SepWP.exists_left; intro e_q192
    apply ProofLib.SepWP.exists_left; intro e_q208; apply ProofLib.SepWP.exists_left; intro e_q224
    apply ProofLib.SepWP.exists_left; intro e_q240; apply ProofLib.SepWP.exists_left; intro e_q256
    apply ProofLib.SepWP.exists_left; intro e_q272; apply ProofLib.SepWP.exists_left; intro e_q288
    apply ProofLib.SepWP.exists_left; intro e_q304; apply ProofLib.SepWP.exists_left; intro e_q320
    apply ProofLib.SepWP.exists_left; intro e_q336; apply ProofLib.SepWP.exists_left; intro e_q352
    apply ProofLib.SepWP.exists_left; intro e_q368; apply ProofLib.SepWP.exists_left; intro e_w384
    apply ProofLib.SepWP.exists_left; intro e_w392
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜(w_tag - 2#64 == 0#64) = false⌝ ∗
      (A.pool lim st s ∗
       (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
          e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
          e_w384 e_w392 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_polyEncoderHeap A.repAlloc enc
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
          e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256 e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
          e_w384 e_w392 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ Rest)) by ac_rfl)) ?_
    apply ProofLib.SepWP.pure_elim; intro htag_ne2
    dsimp only [v3cr_polyEncoderWordsAt]
    rw [sepConj_assoc (((s0.sp - 2400#64) + 1888#64) ↦₆₄ w_tag),
        sepConj_left_comm (A.pool lim st s) (((s0.sp - 2400#64) + 1888#64) ↦₆₄ w_tag)]
    refine SepWP.seq (v3cr_post_enc_1012_ok_placed_budget A lim st (ext := ext)
      s (s0.sp - 2400#64) out w_tag la2 pa4 pa1 la1 ca3 ca2 _
      hfsp_align htag_ne2 hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28) ?_
    intro s2 P2 hpc2 hrun2
      ⟨hP2, _hvm2, hsp2, hx15_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx28_2, htr2⟩
    have h4984 := Variant3dPlacedBudgetAux.v3_ct1Received_ok_4984_to_exit_of_memcpy_placed A lim st hmemcpy_ok s0 s2 out pbA ucSt enc
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
      e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
      e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 Rest
      hsp0_align hpc2 hrun2 hsp2 hx15_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 (htr2.trans htr)
    refine SepWP.weaken_pre (Entails.trans hP2 ?_) (SepWP.mono h4984 ?_)
    · dsimp only [v3cr_polyEncoderWordsAt]
      exact Entails.of_eq (by ac_rfl)
    · intro sm Pm _ _ ⟨hPm, _hvm, hsp_m, hcc_m, htr_m⟩
      exact ⟨[], FreeOnlyEvs.nil, by simpa only [M.stepEvents_nil] using hPm, hsp_m, hcc_m, htr_m⟩

/-- Budget-threaded post-`<PolyEncoder>::from_pb` continuation at `+1012` (`+1012 -> s0.x30`,
    Block `333`) under `FromPbAllocHooksBudget M A lim ext`. -/
theorem v3_ct1Received_post_enc_1012_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (Rest : SepProp)
    (huc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 1012#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = la2)
    (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = ca2)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗
        (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
        (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
        (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
        memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
        resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
          (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs st) sm ∗
            stackAt s0.sp statesFromPbStack ∗ Rest) ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) :=
  v3_ct1Received_post_enc_1012_of_sub_placed
    (Variant2aPlacedBudget.v1_dealloc_ok_at_statesFromPb_placed hA) hA.toPlacedBudget.memcpy_ok
    st s0 s out pbA u ucSt pbEnc ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    Rest huc hsp0_align hpc hrun hsp
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 htr

/-! ## Budget-Threaded `sendingEk = some pbEnc` Composition (`+924 -> s0.x30`) -/

/-- `EncoderFromPbEnv pb` is closed under appending trailing `FreeOnlyEvs`. -/
theorem encoderFromPbEnv_append_freeOnly {pb : ProtoPolynomialEncoder}
    {evs1 evs2 : List AllocEvent}
    (h1 : EncoderFromPbEnv pb evs1) (h2 : FreeOnlyEvs evs2) :
    EncoderFromPbEnv pb (evs1 ++ evs2) := by
  rcases h1 with ⟨ea, ef, rfl, ha, hf⟩
  exact ⟨ea, ef ++ evs2, List.append_assoc ea ef evs2, ha, FreeOnlyEvs.append hf h2⟩

/-- Total-correctness (`SepWP`) budget-threaded `+924 -> lsmpl.base 374 -> +1012 -> s0.x30`
    composition for Variant 3 (`Ct1Received`) with `sendingEk = some pbEnc` and general `Rest`. -/
theorem v3_ct1Received_some_enc_924_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200 : BitVec 64)
    (Rest : SepProp)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)))
    (huc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hpts : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx1 : s.readReg64 .x1 = ca1) (hx8 : s.readReg64 .x8 = w0)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ v96) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        Rest ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            Rest ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h1496_split :
      v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 =
        (((s0.sp - 2400#64) + 1504#64) ↦₆₄ w8) ∗
        ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1512#64) ↦₆₄ w16) ∗
         (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1536#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1544#64) ↦₆₄ w48)) := by
    dsimp only [v1_optProtoPolyEncoderWordsAt]
    simp only [v1_bv_add_add_lit, BitVec.ofNat_eq_ofNat]; ac_rfl
  let Frame924 : SepProp :=
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗
      (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
      ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1512#64) ↦₆₄ w16) ∗
       (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w32) ∗
       (((s0.sp - 2400#64) + 1536#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1544#64) ↦₆₄ w48)) ∗
      memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗ memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ memRegion pbA 112 ∗ memRegion (pbA + 168#64) 56 ∗
      v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
  have hcopy := v3cr_copy_enc_to_call_924_placed_budget A lim st (ext := ext)
    s (s0.sp - 2400#64) out pbA
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w0 w8 w16 w24 w32 w40 w48 v64 v96 v184 v192 v200 e0 e8 e16 e24 e32 e40 e48
    Frame924
    hfsp_align hpc hrun hsp hx0 hx1 hx8 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
  refine SepWP.weaken_pre (by dsimp only [Frame924]; rw [h1496_split]; exact Entails.of_eq (by ac_rfl))
    (seq_clean_lscl_st hcl hcopy ?_)
  intro s1 hpc1 hrun1 hcl1
    ⟨_hvm1, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, _, hx28_1, _, hlr1, htr1⟩
  let FrameCall : SepProp :=
    memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
      memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 296#64) 1592 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      memRegion pbA optProtoInnerStateSize ∗ Rest
  have hpre_pack :
      (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
      v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
      (((s0.sp - 2400#64) + 1504#64) ↦₆₄ w8) ∗
      v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
      v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      A.pool lim st s1 ∗ Frame924 ⊢
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) ∗
       A.pool lim st s1 ∗ stackAt s1.sp encoderFromPbStack) ∗ FrameCall := by
    dsimp only [Frame924, FrameCall]
    rw [hsp1]
    have hpack_enc := v1_optProtoPolyEncoderAt_pack_some A.repAlloc ((s0.sp - 2400#64) + 240#64)
      (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48
    have h400 := v3_collapse_1888_400 (s0.sp - 2400#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    have h1592 := v3_collapse_fsp_296_1592 (s0.sp - 2400#64) w0 w8 w16 w24 w32 w40 w48
    have hpb224 := v3_collapse_pbA_112_224 pbA w0 w8 w16 w24 w32 w40 w48
    refine Entails.trans (Entails.of_eq (show _ =
      (v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 296) ∗
      (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48) ∗
      (memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        ((((s0.sp - 2400#64) + 1504#64) ↦₆₄ w8) ∗
         ((((s0.sp - 2400#64) + 1496#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1512#64) ↦₆₄ w16) ∗
          (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w32) ∗
          (((s0.sp - 2400#64) + 1536#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1544#64) ↦₆₄ w48))) ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336) ∗
      (memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56) ∗
      (A.pool lim st s1 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) by ac_rfl)) ?_
    rw [← h1496_split]
    exact Entails.trans
      (sepConj_mono h400 (sepConj_mono hpack_enc (sepConj_mono h1592 (sepConj_mono_left hpb224))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre_pack ?_
  have hsp1_align : s1.spAligned = true := by
    unfold State.spAligned; rw [hsp1]; exact hfsp_align
  have hpre_ent :
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A.repAlloc ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) ∗
       A.pool lim st s1 ∗ stackAt s1.sp encoderFromPbStack) ⊢
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)).pre
        (⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 240#64, pbToProtoPolyEncoder pbEnc⟩, st) s1 := by
    dsimp only [withLsCodeLoaded, encoderFromPbSpec]
    rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s1.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hcl1
      (Entails.pure_right ⟨hx0_1, hx1_1, hpts, hfits,
        by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s1.readReg64 .x30); rw [show s1.readReg64 .x30 = _ from hlr1]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.call_subroutine_frame hEnc
    (x := (⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 240#64, pbToProtoPolyEncoder pbEnc⟩, st))
    (F := FrameCall)
    hpc1 hrun1 hsp1_align hlr1
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
    (fun _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    ?_
    (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm))
  intro s2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, _, hx28_cs, _, hvregs_cs⟩
  dsimp only [withLsCodeLoaded, encoderFromPbSpec]
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_elim; intro evs1
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr2, _hacp2, henv1⟩
  have h1656 := v3_collapse_fsp_232_1656 (s0.sp - 2400#64)
  have hpost_pack :
      (resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
       memRegion ((s0.sp - 2400#64) + 240#64) protoPolynomialEncoderSize ∗
       A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt s1.sp encoderFromPbStack) ∗
      FrameCall ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
      memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
      (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
      (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 1656 ∗
      resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
        (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest := by
    dsimp only [FrameCall]
    rw [hsp1]
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 240#64) protoPolynomialEncoderSize ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1592) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
       memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
       memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       resultPolyEncoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64)
         (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗
       memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool lim (M.stepEvents evs1 st) s2 ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h1656) (Entails.of_eq (by ac_rfl))
  have h1012 := v3_ct1Received_post_enc_1012_placed hA (M.stepEvents evs1 st) s0 s2 out pbA u ucSt pbEnc
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    Rest huc hsp0_align hpc2 hrun2 (hsp2.trans hsp1)
    (hx19_cs.trans hx19_1) (hx20_cs.trans hx20_1) (hx21_cs.trans hx21_1)
    (hx22_cs.trans hx22_1) (hx23_cs.trans hx23_1) (hx24_cs.trans hx24_1)
    (hx25_cs.trans hx25_1) (hx26_cs.trans hx26_1) (hx28_cs.trans hx28_1)
    ((⟨htr2, hvregs_cs⟩ : TraceCalleeSaved s2 s1).trans (htr1.trans htr))
  refine SepWP.weaken_pre hpost_pack (SepWP.mono h1012 ?_)
  rintro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨evs1 ++ evs2, encoderFromPbEnv_append_freeOnly henv1 hevs2, ?_, hsp_f, hcs_f, htr_f⟩
  rw [← M.stepEvents_append] at hPf
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

/-- `SepWPp` budget-threaded `+924 -> s0.x30` composition for Variant 3 (`Ct1Received`) with
    `sendingEk = some pbEnc`. -/
theorem v3_ct1Received_some_enc_924_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200 : BitVec 64)
    (R : SepProp)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)))
    (huc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hpts : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx1 : s.readReg64 .x1 = ca1) (hx8 : s.readReg64 .x8 = w0)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ v96) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP_ret
    (v3_ct1Received_some_enc_924_placed_sepWP hA hEnc st s0 s hcl out pbA u ucSt pbEnc
      ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200
      statesFromPbJumpTablePlacedAt hfits huc hpts hsp0_align hpc hrun hsp
      hx0 hx1 hx8 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr)

theorem v3_ct1Received_some_enc_924_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200 : BitVec 64)
    (R : SepProp)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv (pbToProtoPolyEncoder pbEnc)))
    (huc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hpts : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx1 : s.readReg64 .x1 = ca1) (hx8 : s.readReg64 .x8 = w0)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ v96) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v3_ct1Received_some_enc_924_placed hA (Variant2aPlacedBudget.encoder_from_pb_ok_of_alloc_placed hA)
    st s0 s hcl out pbA u ucSt pbEnc
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200
    R hfits huc hpts hsp0_align hpc hrun hsp
    hx0 hx1 hx8 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr

theorem v3_ct1Received_some_enc_924_of_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (out pbA : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (pbEnc : PolynomialEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
     w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200 : BitVec 64)
    (R : SepProp)
    (hfits : FitsEnv M lim st (EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc)))
    (huc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u = .ok ucSt)
    (hpts : ∀ bs ∈ pbEnc.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 924#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx0 : s.readReg64 .x0 = pa2) (hx1 : s.readReg64 .x1 = ca1) (hx8 : s.readReg64 .x8 = w0)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa4) (hx22 : s.readReg64 .x22 = pa1)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx24 : s.readReg64 .x24 = la1)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
        memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗ (((s0.sp - 2400#64) + 96#64) ↦₆₄ v96) ∗
        memRegion ((s0.sp - 2400#64) + 104#64) 72 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ (((s0.sp - 2400#64) + 192#64) ↦₆₄ v192) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 16 ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) e0 e8 e16 e24 e32 e40 e48 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1096 ∗ memRegion ((s0.sp - 2400#64) + 1392#64) 104 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1552#64) 336 ∗
        v1_ucWordsAt ((s0.sp - 2400#64) + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion ((s0.sp - 2400#64) + 1992#64) 296 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        memRegion pbA 112 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 168#64) 56 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv (pbToProtoPolyEncoder pbEnc) evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out
              (States.from_pb spqrPolyApi (spqrAuthApi F)
                { innerState := some (.ct1Received { uc := some u, sendingEk := some pbEnc }) }) ∗
            memRegion pbA optProtoInnerStateSize ∗
            statesFromPbJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) :=
  v3_ct1Received_some_enc_924_placed hA hEnc st s0 s hcl out pbA u ucSt pbEnc
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w0 w8 w16 w24 w32 w40 w48 e0 e8 e16 e24 e32 e40 e48 v64 v96 v184 v192 v200
    R (fitsEnv_encoderFromPbAllocEnv_of_encoderFromPbEnv hfits) huc hpts
    hsp0_align hpc hrun hsp
    hx0 hx1 hx8 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudget
