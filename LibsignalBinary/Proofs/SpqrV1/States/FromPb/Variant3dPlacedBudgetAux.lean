/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3cPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 3 Post-Encoder Helpers

Relocatable Block-`333` pure segment lifts (`+924`, `+1012`, `+4984`), `Ok` exit
(`+4984 -> +8180 -> ret`), and `+4884` `FreeOnlyEvs` error exit.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder spqrAuthApi)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesSize optProtoInnerStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (encoderFromPbStack hiBytes7 loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved epilogueOutFull epilogueStackGaps epilogueStackSlots overlapWord7
   resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack
   v1_optProtoPolyEncoderWordsAt v1_ucWordsAt
   v3a_memRegion_608_287_split v3a_pack88
   v3cr_collapse_0_64_72_24 v3cr_epilogueOutFull_ct1Received_close
   v3cr_polyEncoderHeap v3cr_polyEncoderWordsAt v3cr_post_4984_to_epilogue_stack
   v3cr_split_104_72 v3cr_split_208_16 v3cr_split_232_1656
   v3cr_unchunkedEkSentCt1ReceivedHeap)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
  (states_from_pb_epilogue_8180_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (v1_dealloc_ok_of_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3bPlacedBudget
  (v3cr_states_from_pb_err_4884_of_sub_placed v3cr_states_from_pb_err_4968_placed_budget)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

/-! ## `VmPreserved` and Pool-Threading Lifts of `Variant3cPlaced` Segments (Block `333`) -/

/-- `VmPreserved`-strengthened `+924 -> lsmpl.base 374` copy-to-call segment in Block `333`. -/
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
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = ca2 ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 1012#64 ∧
        TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_copy_enc_to_call_924_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      w0 w8 w16 w24 w32 w40 w48 v64 v96 v184 v192 v200 e0 e8 e16 e24 e32 e40 e48 Rest
      hfsp_align (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx0_1) (by simpa using hx1_1) (by simpa using hx8_1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx23_1) (by simpa using hx24_1) (by simpa using hx25_1)
      (by simpa using hx26_1) (by simpa using hx27_1) (by simpa using hx28_1))
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m,
       hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m,
       hx25_m, hx26_m, hx27_m, hx28_m, by simpa using hx29_m, hx30_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_copy_enc_to_call_924_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
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
        v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 64#64) ↦₆₄ uc_ep) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 192#64) ↦₆₄ la4) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
          v1_optProtoPolyEncoderWordsAt (fsp + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
          ((fsp + 1504#64) ↦₆₄ w8) ∗
          v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_ucWordsAt (fsp + 1888#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 1888#64 ∧ sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = ca2 ∧ sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 1012#64 ∧
        TraceCalleeSaved sm s1) := by
  have hwp := v3cr_copy_enc_to_call_924_placed (ext := ext) s1 fsp out pbA
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w0 w8 w16 w24 w32 w40 w48 v64 v96 v184 v192 v200 e0 e8 e16 e24 e32 e40 e48
    (A.pool lim st s1 ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx0_1 hx1_1 hx8_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hregs⟩

/-- `VmPreserved`-strengthened `+1012 -> +1024` error-dispatch segment in Block `333`. -/
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
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_post_enc_1012_err_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pa1 pa4 ca3 ca2 Rest hfsp_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx26_1) (by simpa using hx28_1))
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, hx22_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx19_m, hx21_m, hx22_m, hx26_m, hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_post_enc_1012_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
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
      (((fsp + 1888#64) ↦₆₄ 2#64) ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ 2#64) ∗ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x21 = pa4 ∧
        sm.readReg64 .x22 = pa1 ∧ sm.readReg64 .x26 = ca3 ∧ sm.readReg64 .x28 = ca2 ∧
        TraceCalleeSaved sm s1) := by
  have hwp := v3cr_post_enc_1012_err_placed (ext := ext) s1 fsp out pa1 pa4 ca3 ca2
    (A.pool lim st s1 ∗ Rest) hfsp_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx26_1 hx28_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hregs⟩

/-- `VmPreserved`-strengthened `+1012 -> +4984` `Ok`-dispatch segment in Block `333`. -/
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
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x15 = tag ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_post_enc_1012_ok_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out tag la2 pa4 pa1 la1 ca3 ca2 Rest hfsp_align htag_ne2
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx20_1) (by simpa using hx21_1)
      (by simpa using hx22_1) (by simpa using hx23_1) (by simpa using hx24_1)
      (by simpa using hx25_1) (by simpa using hx26_1) (by simpa using hx28_1))
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx15_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx15_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_post_enc_1012_ok_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
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
      (((fsp + 1888#64) ↦₆₄ tag) ∗ A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x15 = tag ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = la2 ∧ sm.readReg64 .x21 = pa4 ∧ sm.readReg64 .x22 = pa1 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧ sm.readReg64 .x24 = la1 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = ca2 ∧ TraceCalleeSaved sm s1) := by
  have hwp := v3cr_post_enc_1012_ok_placed (ext := ext) s1 fsp out tag la2 pa4 pa1 la1 ca3 ca2
    (A.pool lim st s1 ∗ Rest) hfsp_align htag_ne2 hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hregs⟩

/-- `VmPreserved`-strengthened `+4984 -> +8180` `PolyEncoder` unpack/relocation segment in Block `333`. -/
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
        VmPreserved s1 sm ∧
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
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v3cr_pack_enc_4984_to_8180_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out w_tag ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
      e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80 e_w88 e_w96
      e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
      e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
      e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
      e_w384 e_w392 u160 u208 u232 u172
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      u832 q848 u864 u880 u887 Rest
      hfsp_align (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx15_1) (by simpa using hx19_1) (by simpa using hx20_1)
      (by simpa using hx21_1) (by simpa using hx22_1) (by simpa using hx23_1)
      (by simpa using hx24_1) (by simpa using hx25_1) (by simpa using hx26_1)
      (by simpa using hx28_1))
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx2_m, hx3_m, hx4_m, hx5_m, hx6_m, hx7_m,
       hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hx15_m, hx16_m, hx17_m, hx18_m,
       hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, hx0_m, hx1_m, hx2_m, hx3_m, hx4_m, hx5_m, hx6_m, hx7_m,
       hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hx15_m, hx16_m, hx17_m, hx18_m,
       hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx30_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v3cr_pack_enc_4984_to_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
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
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        A.pool lim st s1 ∗ Rest)
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
            e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
          A.pool lim st sm ∗ Rest) ∧
        VmPreserved s1 sm ∧
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
  have hwp := v3cr_pack_enc_4984_to_8180_placed (ext := ext) s1 fsp out w_tag
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80 e_w88 e_w96
    e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
    e_w384 e_w392 u160 u208 u232 u172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    u832 q848 u864 u880 u887 (A.pool lim st s1 ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx15_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hregs⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hregs⟩

/-! ## Budget-Threaded `Ok` Exit (`+4984 -> +8180 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded Variant-3 `Ok` exit from `+4984` (`+4984 -> +8180 -> s0.x30`, Block `333`)
    under an explicit `memcpy` contract, threading `A.pool lim st` and `VmPreserved`. -/
theorem v3_ct1Received_ok_4984_to_exit_of_memcpy_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (out pbA : BitVec 64)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (enc : PolyEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
     e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
     e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4984#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx15 : s.readReg64 .x15 = w_tag) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = la2) (hx21 : s.readReg64 .x21 = pa4)
    (hx22 : s.readReg64 .x22 = pa1) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24 : s.readReg64 .x24 = la1) (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
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
        v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_polyEncoderHeap A.repAlloc enc
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.ok (.ct1Received { uc := ucSt, sending_ek := enc })) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool lim st sm ∗ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have h104 := v3cr_split_104_72 (s0.sp - 2400#64)
  have h208 := v3cr_split_208_16 (s0.sp - 2400#64)
  have h232 := v3cr_split_232_1656 (s0.sp - 2400#64)
  have h608 := v3a_memRegion_608_287_split (s0.sp - 2400#64)
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono h104
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono h208 (sepConj_mono_right (sepConj_mono
            (Entails.trans h232 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h608)))))))
            (Entails.refl _)))))))))))))) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u887; apply ProofLib.SepWP.exists_left; intro u880
  apply ProofLib.SepWP.exists_left; intro u864; apply ProofLib.SepWP.exists_left; intro q848
  apply ProofLib.SepWP.exists_left; intro u832; apply ProofLib.SepWP.exists_left; intro q816
  apply ProofLib.SepWP.exists_left; intro q800; apply ProofLib.SepWP.exists_left; intro q784
  apply ProofLib.SepWP.exists_left; intro q768; apply ProofLib.SepWP.exists_left; intro q752
  apply ProofLib.SepWP.exists_left; intro q736; apply ProofLib.SepWP.exists_left; intro q720
  apply ProofLib.SepWP.exists_left; intro q704; apply ProofLib.SepWP.exists_left; intro q688
  apply ProofLib.SepWP.exists_left; intro q672; apply ProofLib.SepWP.exists_left; intro q656
  apply ProofLib.SepWP.exists_left; intro q640; apply ProofLib.SepWP.exists_left; intro q624
  apply ProofLib.SepWP.exists_left; intro q608; apply ProofLib.SepWP.exists_left; intro w592
  apply ProofLib.SepWP.exists_left; intro q576; apply ProofLib.SepWP.exists_left; intro bs240
  apply ProofLib.SepWP.exists_left; intro u232; apply ProofLib.SepWP.exists_left; intro u208
  apply ProofLib.SepWP.exists_left; intro d172; apply ProofLib.SepWP.exists_left; intro u160
  apply ProofLib.SepWP.exists_left; intro w120; apply ProofLib.SepWP.exists_left; intro w112
  apply ProofLib.SepWP.exists_left; intro w104
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜bs240.length = 328⌝ ∗
    ((((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
     (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗
     (((s0.sp - 2400#64) + 160#64) ↦₆₄ u160) ∗
     (((s0.sp - 2400#64) + 172#64) ↦₃₂ d172) ∗
     (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
     (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗
     (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
     (((s0.sp - 2400#64) + 208#64) ↦₆₄ u208) ∗
     (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ u232) ∗
     (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ q608) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ q624) ∗
     (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ q640) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ q656) ∗
     (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ q672) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ q688) ∗
     (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ q704) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ q720) ∗
     (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ q736) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ q752) ∗
     (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ q768) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ q784) ∗
     (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ q800) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ q816) ∗
     (((s0.sp - 2400#64) + 832#64) ↦₆₄ u832) ∗ (((s0.sp - 2400#64) + 848#64) ↦₁₂₈ q848) ∗
     (((s0.sp - 2400#64) + 864#64) ↦ₛ loBytes7 u864) ∗
     (((s0.sp - 2400#64) + 880#64) ↦ₛ loBytes7 u880) ∗
     (((s0.sp - 2400#64) + 887#64) ↦₆₄ u887) ∗
     v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
       w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
       e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     A.pool lim st s ∗
     (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ memRegion (s0.sp - 2400#64) 64 ∗
      memRegion ((s0.sp - 2400#64) + 72#64) 24 ∗
      (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
      (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
      memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
      (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
      (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
      (((s0.sp - 2400#64) + 592#64) ↦ₛ loBytes7 w592) ∗
      memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
      memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
      statesFromPbSavedCells s0 ∗
      (v3cr_polyEncoderHeap A.repAlloc enc
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
         e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
         e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion pbA optProtoInnerStateSize ∗ Rest))) by ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; intro hbs240
  refine SepWP.seq (v3cr_pack_enc_4984_to_8180_placed_budget A lim st (ext := ext) s (s0.sp - 2400#64) out
    w_tag ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
    e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392
    u160 u208 u232 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    u832 q848 u864 u880 u887 _
    hfsp_align hpc hrun hsp hx15 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hvm1, hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx7_2,
    hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx14_2, hx15_2, hx16_2, hx17_2, hx18_2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx30_2, htr2⟩
  have hcol := v3cr_collapse_0_64_72_24 (s0.sp - 2400#64) uc_ep
  refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (show _ =
    (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ uc_ep) ∗
     memRegion ((s0.sp - 2400#64) + 72#64) 24) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
     (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ la2) ∗
     (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
     (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
     (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
     (((s0.sp - 2400#64) + 208#64) ↦₆₄ e_w8) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
     (((s0.sp - 2400#64) + 232#64) ↦₆₄ ca2) ∗
     (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ e_q160) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ e_q176) ∗
     (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ e_q192) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ e_q208) ∗
     (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ e_q224) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ e_q240) ∗
     (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ e_q256) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ e_q272) ∗
     (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ e_q288) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ e_q304) ∗
     (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ e_q320) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ e_q336) ∗
     (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ e_q352) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ e_q368) ∗
     (((s0.sp - 2400#64) + 832#64) ↦₆₄ e_w384) ∗
     (((s0.sp - 2400#64) + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
     (((s0.sp - 2400#64) + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
     (((s0.sp - 2400#64) + 864#64) ↦ₛ hiBytes7 e_w152) ∗
     (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
     (((s0.sp - 2400#64) + 888#64) ↦ₛ hiBytes7 e_w120) ∗
     (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
        w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
        e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
        e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
      memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
     (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
     (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
     memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
     (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
     (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
     (((s0.sp - 2400#64) + 592#64) ↦ₛ loBytes7 w592) ∗
     memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
     statesFromPbSavedCells s0 ∗
     (v3cr_polyEncoderHeap A.repAlloc enc
        w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
        e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
        e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
      v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
        ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
      memRegion pbA optProtoInnerStateSize ∗ Rest) ∗
     A.pool lim st s2) by ac_rfl))) ?_
  refine SepWP.weaken_pre (sepConj_mono_left hcol) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d92
  have hstk := v3cr_post_4984_to_epilogue_stack (s0.sp - 2400#64)
    la3 la2 pa3 pa2 la4 ca1 e_w8 ca4 ca2
    d92 w104 w112 w120 bs240 q576 w592
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368
    e_w384 e_w136 e_w144 e_w152 e_w112 e_w120
    w_tag e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80 e_w88 e_w96 e_w104 e_w128 e_w392
  have hstk_pre :
      (memRegion (s0.sp - 2400#64) 92 ∗ (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ la2) ∗
       (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ e_w8) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ca2) ∗
       (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ e_q160) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ e_q176) ∗
       (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ e_q192) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ e_q208) ∗
       (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ e_q224) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ e_q240) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ e_q256) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ e_q272) ∗
       (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ e_q288) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ e_q304) ∗
       (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ e_q320) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ e_q336) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ e_q352) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ e_q368) ∗
       (((s0.sp - 2400#64) + 832#64) ↦₆₄ e_w384) ∗
       (((s0.sp - 2400#64) + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
       (((s0.sp - 2400#64) + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
       (((s0.sp - 2400#64) + 864#64) ↦ₛ hiBytes7 e_w152) ∗
       (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ hiBytes7 e_w120) ∗
       (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗
       statesFromPbSavedCells s0 ∗
       (v3cr_polyEncoderHeap A.repAlloc enc
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        memRegion pbA optProtoInnerStateSize ∗ Rest) ∗
       A.pool lim st s2) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64)
        d92 ((loByte e_w136).zeroExtend 32)
        w104 w112 w120 la2 la4 e_w8 ca4 ca2 bs240 q576 w592
        e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
        e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384
        (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
        (e_w152 >>> 8) (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8)
        (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32 ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (v3cr_polyEncoderHeap A.repAlloc enc
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
         e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
         e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion pbA optProtoInnerStateSize ∗ Rest) ∗
      A.pool lim st s2 := by
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      ((((s0.sp - 2400#64) + 96#64) ↦₆₄ la3) ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ la2) ∗
       (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte e_w136).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ la4) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ ca1) ∗
       (((s0.sp - 2400#64) + 208#64) ↦₆₄ e_w8) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ca2) ∗
       (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ e_q160) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ e_q176) ∗
       (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ e_q192) ∗ (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ e_q208) ∗
       (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ e_q224) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ e_q240) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ e_q256) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ e_q272) ∗
       (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ e_q288) ∗ (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ e_q304) ∗
       (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ e_q320) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ e_q336) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ e_q352) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ e_q368) ∗
       (((s0.sp - 2400#64) + 832#64) ↦₆₄ e_w384) ∗
       (((s0.sp - 2400#64) + 848#64) ↦₆₄ unshiftWord e_w136 (loByte e_w144)) ∗
       (((s0.sp - 2400#64) + 856#64) ↦₆₄ unshiftWord e_w144 (loByte e_w152)) ∗
       (((s0.sp - 2400#64) + 864#64) ↦ₛ hiBytes7 e_w152) ∗
       (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord e_w112 (loByte e_w120)) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ hiBytes7 e_w120) ∗
       (v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
       memRegion (s0.sp - 2400#64) 92 ∗ (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗
       (((s0.sp - 2400#64) + 104#64) ↦₆₄ w104) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ w112) ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ w120) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ memRegion ((s0.sp - 2400#64) + 216#64) 8 ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗
       (((s0.sp - 2400#64) + 592#64) ↦ₛ loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993) ∗
      statesFromPbSavedCells s0 ∗
      (v3cr_polyEncoderHeap A.repAlloc enc
         w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
         e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
         e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
         e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
       v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
         ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
       memRegion pbA optProtoInnerStateSize ∗ Rest) ∗
      A.pool lim st s2 by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
      (Entails.of_eq (by ac_rfl))
  have hep := Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed A lim st hmemcpy_ok s0 s2 out
    d92 ((loByte e_w136).zeroExtend 32)
    w104 w112 w120 la2 la4 e_w8 ca4 ca2 bs240 hbs240 q576 w592
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384
    (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
    (e_w152 >>> 8) (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8)
    (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32
    (v3cr_polyEncoderHeap A.repAlloc enc
       w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
       e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
       ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
     memRegion pbA optProtoInnerStateSize ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 (htr2.trans htr)
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hstk_pre) (SepWP.mono hep ?_)
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m, hvm2⟩
  dsimp only [State.readReg32] at hPm hx3_2 hx21_2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2,
      hx0_2, hx3_2, hx27_2, hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2,
      hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2] at hPm
  have hclose := v3cr_epilogueOutFull_ct1Received_close A.repAlloc (F := F) out ucSt enc
    w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
    e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392
    ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w104 w112 w120 (d92.setWidth 8) q576
    (overlapWord7 (q576.extractLsb' 64 64) w592) bs240 hbs240
    (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32
  refine ⟨Entails.trans hPm ?_, hvm1.trans hvm2, hsp_m, hcc_m, htr_m⟩
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueOutFull out
       5#64 w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72 e_w80
       (((e_w88.extractLsb' 0 8).zeroExtend 32).setWidth 8)
       ((v3a_pack88 e_w88).setWidth 32)
       (((v3a_pack88 e_w88 >>> 32).setWidth 32).setWidth 16)
       (((v3a_pack88 e_w88 >>> 48).setWidth 32).setWidth 8)
       e_w96 e_w104
       (((loByte e_w112).zeroExtend 32).setWidth 8)
       (unshiftWord e_w112 (loByte e_w120))
       (overlapWord7 (unshiftWord e_w112 (loByte e_w120)) (e_w120 >>> 8))
       e_w128
       (((loByte e_w136).zeroExtend 32).setWidth 8)
       (unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144))
       (overlapWord7
         ((unshiftWord e_w144 (loByte e_w152) ++ unshiftWord e_w136 (loByte e_w144)).extractLsb' 64 64)
         (e_w152 >>> 8))
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392
       ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
       w104 w112 w120 (d92.setWidth 8) q576
       (overlapWord7 (q576.extractLsb' 64 64) w592) bs240
       (e_w8 ++ w_tag) (e_w24 ++ e_w16) e_w32 ∗
     v3cr_polyEncoderHeap A.repAlloc enc
       w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
       e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
       e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
       e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
     v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
       ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep) ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool lim st sm ∗ stackAt s0.sp statesFromPbStack ∗ Rest) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hclose) (Entails.of_eq (by ac_rfl))

/-- Budget-threaded Variant-3 `Ok` exit from `+4984` (`+4984 -> +8180 -> s0.x30`, Block `333`)
    under `FromPbAllocHooksBudget M A lim ext`. -/
theorem v3_ct1Received_ok_4984_to_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (ucSt : CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) (enc : PolyEncoder)
    (ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep : BitVec 64)
    (w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
     e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152 : BitVec 64)
    (e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
     e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 : BitVec 128)
    (e_w384 e_w392 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4984#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx15 : s.readReg64 .x15 = w_tag) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = la2) (hx21 : s.readReg64 .x21 = pa4)
    (hx22 : s.readReg64 .x22 = pa1) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24 : s.readReg64 .x24 = la1) (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = ca2) (htr : TraceCalleeSaved s s0) :
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
        v3cr_polyEncoderWordsAt ((s0.sp - 2400#64) + 1888#64)
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        v3cr_polyEncoderHeap A.repAlloc enc
          w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64
          e_w72 e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
          e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
          e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 ∗
        v3cr_unchunkedEkSentCt1ReceivedHeap A.repAlloc (F := F) ucSt
          ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool lim st s ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.ok (.ct1Received { uc := ucSt, sending_ek := enc })) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool lim st sm ∗ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        VmPreserved s sm ∧ sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) :=
  v3_ct1Received_ok_4984_to_exit_of_memcpy_placed A lim st hA.toPlacedBudget.memcpy_ok
    s0 s out pbA ucSt enc ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 ca4 pa4 la4 uc_ep
    w_tag e_w8 e_w16 e_w24 e_w32 e_w40 e_w48 e_w56 e_w64 e_w72
    e_w80 e_w88 e_w96 e_w104 e_w112 e_w120 e_w128 e_w136 e_w144 e_w152
    e_q160 e_q176 e_q192 e_q208 e_q224 e_q240 e_q256
    e_q272 e_q288 e_q304 e_q320 e_q336 e_q352 e_q368 e_w384 e_w392 Rest
    hsp0_align hpc hrun hsp hx15 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx28 htr

/-! ## Budget-Threaded `+4884 -> +4968 -> s0.x30` 4-Vector Dealloc Exit (`sendingEk = none`) -/

private theorem memRegion_2304_of_4884 (fsp pa3 ca4 : BitVec 64) :
    memRegion fsp 176 ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      memRegion (fsp + 184#64) 40 ∗
      ((fsp + 224#64) ↦₆₄ ca4) ∗
      memRegion (fsp + 232#64) 2072 ⊢
    memRegion fsp 2304 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 176) (k := 2128) (b' := fsp + 176#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 176#64) (n := 8) (k := 2120) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 40) (k := 2080) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 8) (k := 2072) (b' := fsp + 232#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))

/-- Budget-threaded `+4884 -> +4968 -> s0.x30` 4-vector dealloc error exit (`sendingEk = none`)
    under an explicit Block-`333` `__rust_dealloc` contract, emitting `FreeOnlyEvs`. -/
theorem v3_ct1Received_err_4884_to_exit_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx1 : s.readReg64 .x1 = ca1)
    (hx22 : s.readReg64 .x22 = pa1) (hx0 : s.readReg64 .x0 = pa2)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
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
  have h4884 := v3cr_states_from_pb_err_4884_of_sub_placed hdealloc_ok st s0 s out
    ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4
    (memRegion (s0.sp - 2400#64) 176 ∗
     memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
     memRegion ((s0.sp - 2400#64) + 232#64) 2072 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ Rest)
    hsp0_align hpc hrun hsp hx19 hx1 hx22 hx0 hx28 hx26 hx21 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) h4884) ?_
  rintro s2 P2 hpc2 hrun2 ⟨evs, hevs, hP2, hsp2, hx19_2, hx22_2, htr2⟩
  have h2304 := memRegion_2304_of_4884 (s0.sp - 2400#64) pa3 ca4
  have hP2' : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      A.pool lim (M.stepEvents evs st) s2 ∗
      (memRegion pbA optProtoInnerStateSize ∗ Rest) := by
    refine Entails.trans hP2 ?_
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (memRegion (s0.sp - 2400#64) 176 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
       memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
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

theorem v3_ct1Received_err_4884_to_exit_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx1 : s.readReg64 .x1 = ca1)
    (hx22 : s.readReg64 .x22 = pa1) (hx0 : s.readReg64 .x0 = pa2)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
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
  v3_ct1Received_err_4884_to_exit_of_sub_placed (v1_dealloc_ok_of_dealloc_placed hdealloc)
    st s0 s out pbA ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc hrun hsp hx19 hx1 hx22 hx0 hx28 hx26 hx21 htr

/-- Budget-threaded `+4884 -> +4968 -> s0.x30` 4-vector dealloc error exit under
    `FromPbAllocHooksBudget M A lim ext`. -/
theorem v3_ct1Received_err_4884_to_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ) (s0 s : State) (out pbA : BitVec 64)
    (ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4884#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx1 : s.readReg64 .x1 = ca1)
    (hx22 : s.readReg64 .x22 = pa1) (hx0 : s.readReg64 .x0 = pa2)
    (hx28 : s.readReg64 .x28 = ca2) (hx26 : s.readReg64 .x26 = ca3)
    (hx21 : s.readReg64 .x21 = pa4) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 176 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗
        memRegion ((s0.sp - 2400#64) + 184#64) 40 ∗
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
  v3_ct1Received_err_4884_to_exit_of_dealloc_placed hA.dealloc st s0 s out pbA
    ca1 pa1 ca2 pa2 ca3 pa3 ca4 pa4 Rest
    hsp0_align hpc hrun hsp hx19 hx1 hx22 hx0 hx28 hx26 hx21 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant3dPlacedBudgetAux
