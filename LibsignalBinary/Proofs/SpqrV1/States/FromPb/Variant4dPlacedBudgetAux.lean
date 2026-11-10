/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 4 Segment and Cleanup Helpers

Pool-threading lifts of `Variant4bPlaced` steps and `FreeOnlyEvs` cleanup helpers
(`+5264 -> ret` and `+304 -> +5276`) in Block `333`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 lsProg_333 ls_blockPlacement_base lsmpl)
open CryptoVerification.LibsignalSpqrV1 (Error ProtoPolynomialDecoder V1State)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecU8)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells
   statesFromPbStack v4_Saved5276Preserved v4_stackAt_allocHook_to_encoderFromPbStack
   v4_stackAt_encoderFromPbStack_to_allocHook v4b_optProtoAuthHeap
   v4b_optProtoPolyDecoderHeap v4b_optProtoPolyDecoderWordsAt v4b_optProtoUcHeap
   v4b_optProtoUcWordsAt v4b_vecU8Heap v4b_vecU8Heap_entails_dealloc
   v4d_fsp_aligned v4d_sepWP_pure_left)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_evs)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

/-! ## `VmPreserved` & Pool-Threading Lifts of `Variant4bPlaced` Steps -/

theorem v4b_step_248_none_to_2228_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2228#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = noneCap ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4b_step_248_none_to_2228_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
      d8 d16 d24 d28 d32 (Frame ∗ A.pool lim st s)
      (by simpa using hpc) (by simpa using hrun) (by simpa using hx27))
    fun s' P' hvm ⟨hP', hsp', hx0, hx1, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15,
        hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27', hx28, htr⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, by simpa using hsp', by simpa using hx0, by simpa using hx1,
    by simpa using hx8, by simpa using hx9, by simpa using hx10, by simpa using hx11,
    by simpa using hx12, by simpa using hx13, by simpa using hx14, by simpa using hx15,
    by simpa using hx19, by simpa using hx20, by simpa using hx21, by simpa using hx22,
    by simpa using hx23, by simpa using hx24, by simpa using hx25, by simpa using hx26,
    by simpa using hx27', by simpa using hx28,
    ⟨by simpa using htr.1, by simpa using htr.2⟩⟩

theorem v4b_step_2228_none_to_5264_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 2228#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = noneCap) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5264#64) s
      (Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧
        s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x24 = s.readReg64 .x24 ∧
        s'.readReg64 .x26 = 0#64 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4b_step_2228_none_to_5264_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      (Frame ∗ A.pool lim st s)
      (by simpa using hpc) (by simpa using hrun) (by simpa using hx22))
    fun s' P' hvm ⟨hP', hsp', hx14, hx15, hx19, hx20, hx24, hx26, hx28, htr⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, by simpa using hsp', by simpa using hx14, by simpa using hx15,
    by simpa using hx19, by simpa using hx20, by simpa using hx24,
    by simpa using hx26, by simpa using hx28,
    ⟨by simpa using htr.1, by simpa using htr.2⟩⟩

theorem v4b_step_248_some_eq_to_2228_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 2228#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = 80#64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4b_step_248_some_eq_to_2228_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
      d0 d8 d16 d28 d32 (Frame ∗ A.pool lim st s) hd0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hx27))
    fun s' P' hvm ⟨hP', hsp', hx0, hx1, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15,
        hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27', hx28, htr⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, by simpa using hsp', by simpa using hx0, by simpa using hx1,
    by simpa using hx8, by simpa using hx9, by simpa using hx10, by simpa using hx11,
    by simpa using hx12, by simpa using hx13, by simpa using hx14, by simpa using hx15,
    by simpa using hx19, by simpa using hx20, by simpa using hx21, by simpa using hx22,
    by simpa using hx23, by simpa using hx24, by simpa using hx25, by simpa using hx26,
    by simpa using hx27', by simpa using hx28,
    ⟨by simpa using htr.1, by simpa using htr.2⟩⟩

theorem v4b_step_248_some_ne_to_304_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hd24_ne : d24 ≠ 80#32)
    (hpc : s.pc = lsmpl.base 333 + 248#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 304#64) s
      (v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = s.sp ∧
        s'.readReg64 .x0 = u56 ∧
        s'.readReg64 .x1 = u48 ∧
        s'.readReg64 .x8 = u16 ∧
        s'.readReg64 .x9 = u40 ∧
        s'.readReg64 .x10 = u64 ∧
        s'.readReg64 .x11 = u8 ∧
        s'.readReg64 .x12 = u32 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = d28.zeroExtend 64 ∧
        s'.readReg64 .x15 = d32 ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4b_step_248_some_ne_to_304_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
      d0 d8 d16 d24 d28 d32 (Frame ∗ A.pool lim st s) hd0_lt hd24_ne
      (by simpa using hpc) (by simpa using hrun) (by simpa using hx27))
    fun s' P' hvm ⟨hP', hsp', hx0, hx1, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15,
        hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27', hx28, htr⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, by simpa using hsp', by simpa using hx0, by simpa using hx1,
    by simpa using hx8, by simpa using hx9, by simpa using hx10, by simpa using hx11,
    by simpa using hx12, by simpa using hx13, by simpa using hx14, by simpa using hx15,
    by simpa using hx19, by simpa using hx20, by simpa using hx21, by simpa using hx22,
    by simpa using hx23, by simpa using hx24, by simpa using hx25, by simpa using hx26,
    by simpa using hx27', by simpa using hx28,
    ⟨by simpa using htr.1, by simpa using htr.2⟩⟩

/-- Pool-threading copy + `bl` at `+2228..+2304 -> lsmpl.base 348` (`ekSentCt1ReceivedFromPb`). -/
theorem v4b_step_2228_some_to_18368_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp pbA out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u : BitVec 64)
    (v224 : BitVec 64) (v232 : BitVec 32)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hu0_lt : u0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u56)
    (hx1 : s.readReg64 .x1 = u48)
    (hx8 : s.readReg64 .x8 = u16)
    (hx9 : s.readReg64 .x9 = u40)
    (hx10 : s.readReg64 .x10 = u64)
    (hx11 : s.readReg64 .x11 = u8)
    (hx12 : s.readReg64 .x12 = u32)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64)
    (hx14 : s.readReg64 .x14 = d28.zeroExtend 64)
    (hx15 : s.readReg64 .x15 = d32)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx21 : s.readReg64 .x21 = u24)
    (hx22 : s.readReg64 .x22 = u0)
    (hx23 : s.readReg64 .x23 = d24.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = d8)
    (hx25 : s.readReg64 .x25 = u80)
    (hx26 : s.readReg64 .x26 = u72)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 348) s
      (((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
        ((fsp + 224#64) ↦₆₄ v224) ∗ ((fsp + 232#64) ↦₃₂ v232) ∗
        v4b_optProtoUcWordsAt (fsp + 1392#64)
          s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ ((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
          v4b_optProtoUcWordsAt (fsp + 1392#64)
            u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = fsp + 1888#64 ∧
        s'.readReg64 .x1 = fsp + 1392#64 ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x21 = u24 ∧
        s'.readReg64 .x22 = u0 ∧
        s'.readReg64 .x23 = d24.zeroExtend 64 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x25 = u80 ∧
        s'.readReg64 .x26 = u72 ∧
        s'.readReg64 .x27 = pbA ∧
        s'.readReg64 .x28 = d0 ∧
        s'.readReg64 .x30 = lsmpl.base 333 + 2308#64 ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4b_step_2228_some_to_18368_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp pbA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
      s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u
      v224 v232 d0 d8 d16 d24 d28 d32 (Frame ∗ A.pool lim st s) hfsp_align hu0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx0) (by simpa using hx1) (by simpa using hx8) (by simpa using hx9)
      (by simpa using hx10) (by simpa using hx11) (by simpa using hx12) (by simpa using hx13)
      (by simpa using hx14) (by simpa using hx15) (by simpa using hx19) (by simpa using hx20)
      (by simpa using hx21) (by simpa using hx22) (by simpa using hx23) (by simpa using hx24)
      (by simpa using hx25) (by simpa using hx26) (by simpa using hx27) (by simpa using hx28))
    fun s' P' hvm ⟨hP', hsp', hx0', hx1', hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx28', hx30', htr⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, by simpa using hsp', by simpa using hx0', by simpa using hx1',
    by simpa using hx19', by simpa using hx20', by simpa using hx21', by simpa using hx22',
    by simpa using hx23', by simpa using hx24', by simpa using hx25', by simpa using hx26',
    by simpa using hx27', by simpa using hx28',
    by rw [← ls_blockPlacement_base (i := 333)]; simpa using hx30',
    ⟨by simpa using htr.1, by simpa using htr.2⟩⟩

theorem v4b_step_2308_err_to_5264_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out d0 d8 d16 : BitVec 64) (d28 : BitVec 32)
    (w1896 w1904 w1912 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5264#64) s
      (((fsp + 232#64) ↦₃₂ d28) ∗
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗
        ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗
        ((fsp + 1912#64) ↦₆₄ w1912) ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ ((fsp + 232#64) ↦₃₂ d28) ∗
          ((fsp + 1888#64) ↦₆₄ noneCap) ∗
          ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗
          ((fsp + 1912#64) ↦₆₄ w1912) ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = d16 ∧
        s'.readReg64 .x24 = d8 ∧
        s'.readReg64 .x26 = w1896 ∧
        s'.readReg64 .x28 = d0 ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4b_step_2308_err_to_5264_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out d0 d8 d16 d28 w1896 w1904 w1912 (Frame ∗ A.pool lim st s) hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx24) (by simpa using hx28))
    fun s' P' hvm ⟨hP', hsp', hx19', hx20', hx24', hx26', hx28', htr⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, by simpa using hsp', by simpa using hx19', by simpa using hx20',
    by simpa using hx24', by simpa using hx26', by simpa using hx28',
    ⟨by simpa using htr.1, by simpa using htr.2⟩⟩

/-- Pool-threading `Ok(uc)` + `receivingCt2 = none` branch (`+2308..+2368 -> +6860`). -/
theorem v4b_step_2308_ok_none_to_6860_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (v72 v128 v144 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = noneCap) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6860#64) s
      (((fsp + 72#64) ↦₆₄ v72) ∗
        ((fsp + 128#64) ↦₆₄ v128) ∗
        ((fsp + 144#64) ↦₆₄ v144) ∗
        v4b_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          v4b_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = mkPtr ∧
        s'.readReg64 .x1 = mkCap ∧
        s'.readReg64 .x9 = rkCap ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x26 = rkPtr ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4b_step_2308_ok_none_to_6860_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch
      v72 v128 v144 (Frame ∗ A.pool lim st s) hfsp_align hrk_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx28))
    fun s' P' hvm ⟨hP', hsp', hx0', hx1', hx9', hx19', hx22', hx26', htr⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, by simpa using hsp', by simpa using hx0', by simpa using hx1',
    by simpa using hx9', by simpa using hx19', by simpa using hx22', by simpa using hx26',
    ⟨by simpa using htr.1, by simpa using htr.2⟩⟩

/-! ## Shared `+5264 -> +5348 -> ret` Cleanup & `+304 -> +5276` `optUc` Drop -/

/-- From `+5264`, deallocate `optDec : Option ProtoPolynomialDecoder` (`d0, d8, d16, d24, d28, d32`)
    under `FreeOnlyEvs` and exit via `+5348` with `.error (.err err)`. -/
theorem v4d_dealloc_opt_dec_5264_to_ret_of_placedHooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s : State) (out d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (err : Error)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0)
    (hx26 : (s.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    v4d_fsp_aligned s0.sp hsp0_align
  cases optDec with
  | none =>
    dsimp only [v4b_optProtoPolyDecoderHeap]
    apply v4d_sepWP_pure_left; rintro rfl
    have h5264 := Variant4aPlacedBudget.v4_states_from_pb_dealloc_none_proto_decoder_5264_placed_budget
      A lim st (ext := ext) s0 s (s0.sp - 2400#64) out d8 (s.readReg64 .x26)
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      hpc hrun hsp hx19 hx24 hx28 rfl htr
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq h5264 ?_)
    intro s1 P1 hpc1 hrun1 ⟨hP1, _hvm1, hsp1, hx19_1, _, _, hx26_1, htr1⟩
    have hx26_1' : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err := by
      rw [hx26_1, hx26]
    have herr := Variant4aPlacedBudget.v4_states_from_pb_err_5348_placed_budget
      A lim st (F := F) (ext := ext) s0 s1 out err Rest
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1' htr1
    refine SepWP.weaken_pre (Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl)))
      (SepWP.mono herr fun sf Pf _ _ ⟨hPf, _hvmf, hsp_f, hcs_f, htr_f⟩ => ?_)
    refine ⟨[], FreeOnlyEvs.nil, ?_, hsp_f, hcs_f, htr_f⟩
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))
  | some pb =>
    dsimp only [v4b_optProtoPolyDecoderHeap]
    rw [sepConj_assoc]
    apply v4d_sepWP_pure_left; rintro ⟨rfl, rfl, rfl, hle, hcap, _, _⟩
    have hpre_split :
        (if d0 = 0#64 then emp
         else A.repAlloc.live d8 (d0.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 d8 pb.pts ∗
           memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool lim st s ∗ Rest ⊢
        (if d0 = 0#64 then emp
         else A.live d8 (d0.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 d8 pb.pts ∗
           memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
          A.pool lim st s ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           Rest) := by
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hpre_split ?_
    have h5264 := Variant4aPlacedBudget.v4_states_from_pb_dealloc_some_proto_decoder_5264_placed
      hA s0 s (s0.sp - 2400#64) out d8 d0 (s.readReg64 .x26) pb.pts st
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗
       Rest)
      hfsp_align hle hcap hpc hrun hsp hx19 hx24 hx28 rfl hx20 htr
    refine seq_clean_evs h5264 ?_
    intro evs s1 hevs hpc1 hrun1 ⟨hsp1, hx19_1, _, _, hx26_1, htr1⟩
    have hx26_1' : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err := by
      rw [hx26_1, hx26]
    have hpre_join :
        A.pool lim (M.stepEvents evs st) s1 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
          (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           Rest) ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          Rest ∗ A.pool lim (M.stepEvents evs st) s1 := by
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
          (memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           memRegion out chunkedStatesSize ∗
           Rest ∗ A.pool lim (M.stepEvents evs st) s1) by sep_ac_rfl)) ?_
      exact sepConj_mono_left (v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    have herr := Variant4aPlacedBudget.v4_states_from_pb_err_5348_placed_budget
      A lim (M.stepEvents evs st) (F := F) (ext := ext) s0 s1 out err Rest
      hsp0_align hpc1 hrun1 hsp1 hx19_1 hx26_1' htr1
    refine SepWP.weaken_pre hpre_join (SepWP.mono herr ?_)
    intro sf Pf _ _ ⟨hPf, _hvmf, hsp_f, hcs_f, htr_f⟩
    exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem v4d_dealloc_opt_dec_5264_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s : State) (out d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (optDec : Option ProtoPolynomialDecoder)
    (err : Error)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0)
    (hx26 : (s.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (v4b_optProtoPolyDecoderHeap A.repAlloc optDec d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool lim st s ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
            (A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∗
            stackAt s0.sp statesFromPbStack) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  v4d_dealloc_opt_dec_5264_to_ret_of_placedHooks_placed hA.toPlacedBudget st
    s0 s out d0 d8 d16 d32 d24 d28 optDec err Rest
    hsp0_align hpc hrun hsp hx19 hx20 hx24 hx28 hx26 htr

/-- From `+304`, drop `optUc : Option V1State.Unchunked.EkSentCt1Received` under `FreeOnlyEvs`
    and reach `+5276` with `x26 = 2#64` (`spqrErrorByte .msgDecode`). -/
theorem v4d_drop_opt_uc_304_to_5276_of_placedHooks_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s : State) (fsp out ptsPtr ptsCap x20_val : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u56)
    (hx1 : s.readReg64 .x1 = u48)
    (hx11 : s.readReg64 .x11 = u8)
    (hx12 : s.readReg64 .x12 = u32)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = u24)
    (hx22 : s.readReg64 .x22 = u0)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx25 : s.readReg64 .x25 = u80)
    (hx26 : s.readReg64 .x26 = u72)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5276#64) s
      (v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x20 = x20_val) := by
  cases optUc with
  | none =>
    dsimp only [v4b_optProtoUcHeap]
    apply v4d_sepWP_pure_left; rintro rfl
    have hnone := Variant4aPlacedBudget.v4_states_from_pb_drop_proto_uc_none_304_placed_budget
      A lim st (ext := ext) s0 s fsp out ptsPtr ptsCap x20_val
      (stackAt fsp allocHookStack ∗ Frame)
      hpc hrun hsp hx19 hx20 hx22 hx24 hx28 htr
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hnone ?_)
    intro sm Pm _ _ ⟨hPm, _hvm, hpres, hx20_m⟩
    refine ⟨[], FreeOnlyEvs.nil, ?_, hpres, hx20_m⟩
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    exact Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))
  | some u =>
    cases hauth : u.auth with
    | none =>
      dsimp only [v4b_optProtoUcHeap]
      rw [hauth]
      dsimp only [v4b_optProtoAuthHeap]
      have hdealloc :
          (v4b_vecU8Heap A.repAlloc u.dk u0 u8 u16 ∗
           v4b_vecU8Heap A.repAlloc u.ct1 u24 u32 u40 ∗
           ⌜u48 = noneCap⌝ ∗ ⌜u96 = u.epoch⌝) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame ⊢
          ⌜u0.toNat < 2 ^ 63 ∧ u48 = noneCap⌝ ∗
          (vecCapPtrDealloc A.repAlloc u0 u8 ∗
           vecCapPtrDealloc A.repAlloc u24 u32 ∗
           A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) := by
        refine Entails.trans
          (sepConj_mono_left
            (sepConj_mono (v4b_vecU8Heap_entails_dealloc A.repAlloc u.dk u0 u8 u16)
              (sepConj_mono_left (v4b_vecU8Heap_entails_dealloc A.repAlloc u.ct1 u24 u32 u40)))) ?_
        refine Entails.trans (Entails.of_eq (show _ =
          ⌜u0.toNat < 2 ^ 63⌝ ∗ ⌜u24.toNat < 2 ^ 63⌝ ∗ ⌜u48 = noneCap⌝ ∗ ⌜u96 = u.epoch⌝ ∗
          (vecCapPtrDealloc A.repAlloc u0 u8 ∗ vecCapPtrDealloc A.repAlloc u24 u32 ∗
           A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
        apply Entails.pure_left; intro hu0
        apply Entails.pure_left; intro _
        apply Entails.pure_left; intro hu48
        apply Entails.pure_left; intro _
        exact Entails.pure_right ⟨hu0, hu48⟩ (Entails.refl _)
      refine SepWP.weaken_pre hdealloc ?_
      apply v4d_sepWP_pure_left; rintro ⟨hu0_lt, rfl⟩
      exact Variant4aPlacedBudget.v4_states_from_pb_drop_proto_uc_none_auth_304_placed hA s0 s
        fsp out ptsPtr ptsCap x20_val u8 u0 u32 u24 st Frame
        hfsp_align hu0_lt hpc hrun hsp hx1 hx11 hx12 hx19 hx20 hx21 hx22 hx24 hx28 htr
    | some auth =>
      dsimp only [v4b_optProtoUcHeap]
      rw [hauth]
      dsimp only [v4b_optProtoAuthHeap]
      have hdealloc :
          (v4b_vecU8Heap A.repAlloc u.dk u0 u8 u16 ∗
           v4b_vecU8Heap A.repAlloc u.ct1 u24 u32 u40 ∗
           (v4b_vecU8Heap A.repAlloc auth.rootKey u48 u56 u64 ∗
            v4b_vecU8Heap A.repAlloc auth.macKey u72 u80 u88) ∗
           ⌜u96 = u.epoch⌝) ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame ⊢
          ⌜u0.toNat < 2 ^ 63 ∧ u48.toNat < 2 ^ 63⌝ ∗
          (vecCapPtrDealloc A.repAlloc u48 u56 ∗
           vecCapPtrDealloc A.repAlloc u72 u80 ∗
           vecCapPtrDealloc A.repAlloc u0 u8 ∗
           vecCapPtrDealloc A.repAlloc u24 u32 ∗
           A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) := by
        refine Entails.trans
          (sepConj_mono_left
            (sepConj_mono (v4b_vecU8Heap_entails_dealloc A.repAlloc u.dk u0 u8 u16)
              (sepConj_mono (v4b_vecU8Heap_entails_dealloc A.repAlloc u.ct1 u24 u32 u40)
                (sepConj_mono_left
                  (sepConj_mono (v4b_vecU8Heap_entails_dealloc A.repAlloc auth.rootKey u48 u56 u64)
                    (v4b_vecU8Heap_entails_dealloc A.repAlloc auth.macKey u72 u80 u88)))))) ?_
        refine Entails.trans (Entails.of_eq (show _ =
          ⌜u0.toNat < 2 ^ 63⌝ ∗ ⌜u24.toNat < 2 ^ 63⌝ ∗ ⌜u48.toNat < 2 ^ 63⌝ ∗
          ⌜u72.toNat < 2 ^ 63⌝ ∗ ⌜u96 = u.epoch⌝ ∗
          (vecCapPtrDealloc A.repAlloc u48 u56 ∗ vecCapPtrDealloc A.repAlloc u72 u80 ∗
           vecCapPtrDealloc A.repAlloc u0 u8 ∗ vecCapPtrDealloc A.repAlloc u24 u32 ∗
           A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
        apply Entails.pure_left; intro hu0
        apply Entails.pure_left; intro _
        apply Entails.pure_left; intro hu48
        apply Entails.pure_left; intro _
        apply Entails.pure_left; intro _
        exact Entails.pure_right ⟨hu0, hu48⟩ (Entails.refl _)
      refine SepWP.weaken_pre hdealloc ?_
      apply v4d_sepWP_pure_left; rintro ⟨hu0_lt, hu48_lt⟩
      exact Variant4aPlacedBudget.v4_states_from_pb_drop_proto_uc_some_auth_304_placed hA s0 s
        fsp out ptsPtr ptsCap x20_val u56 u48 u80 u72 u8 u0 u32 u24 st Frame
        hfsp_align hu0_lt hu48_lt hpc hrun hsp
        hx0 hx1 hx11 hx12 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 htr

theorem v4d_drop_opt_uc_304_to_5276_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) (st : M.σ)
    (s0 s : State) (fsp out ptsPtr ptsCap x20_val : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (optUc : Option V1State.Unchunked.EkSentCt1Received)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = u56)
    (hx1 : s.readReg64 .x1 = u48)
    (hx11 : s.readReg64 .x11 = u8)
    (hx12 : s.readReg64 .x12 = u32)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = u24)
    (hx22 : s.readReg64 .x22 = u0)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx25 : s.readReg64 .x25 = u80)
    (hx26 : s.readReg64 .x26 = u72)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5276#64) s
      (v4b_optProtoUcHeap A.repAlloc optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
          sm.readReg64 .x20 = x20_val) :=
  v4d_drop_opt_uc_304_to_5276_of_placedHooks_placed hA.toPlacedBudget st
    s0 s fsp out ptsPtr ptsCap x20_val
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 optUc Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx11 hx12 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx28 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4dPlacedBudgetAux
