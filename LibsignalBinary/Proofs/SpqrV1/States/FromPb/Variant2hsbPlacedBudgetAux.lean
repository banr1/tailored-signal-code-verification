/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`) Pure Segment Lifts

Relocatable Block-`333` pure segments (`+508`, `+592`, `+3348`, `+8944`) strengthened with
`VmPreserved` and `RustCliAllocBudget M` pool preservation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement blkLib_eq_333 lsProg_333 lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v1_optProtoPolyEncoderWordsAt v2hs_ekSentWordsAt
   v2hs_optProtoDecoderWordsAt v2hs_pb128At v2hs_ucWordsAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

/-! ## `VmPreserved` & Pool-Threaded PB-to-Stack Copy (`+508 -> +3348 / +592`) -/

theorem v2hs_copy_pb_to_stack_508_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (d_w0 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 3348#64
       else lsmpl.base 333 + 592#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64)
            d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
            w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v2hs_copy_pb_to_stack_508_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 Rest
      hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx19_2, hx21_2, hx27_2, hx22_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx19_2,
       by simpa using hx21_2, by simpa using hx27_2, by simpa using hx22_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v2hs_copy_pb_to_stack_508_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 508#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (d_w0 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 3348#64
       else lsmpl.base 333 + 592#64)
      s1
      (memRegion (s0.sp - 2400#64) 2304 ∗
        v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
          w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        Rest ∗ A.pool lim st s1)
      (fun s2 P2 =>
        (P2 ⊢
          memRegion (s0.sp - 2400#64) 896 ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64)
            w0 w8 w16 w24 w32 w40 w48 ∗
          v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64)
            d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
          v2hs_pb128At (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
            w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          Rest ∗ A.pool lim st s2) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x27 = pbA ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v2hs_copy_pb_to_stack_508_placed (ext := ext)
    s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w0 w8 w16 w24 w32 w40 w48 d_w0 d_w8 d_w16 d_w24 d_w32 (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

/-! ## `VmPreserved` & Pool-Threaded `ptsNeeded == 480` Check (`+592 -> +3348 / +604`) -/

theorem v2hs_check_ptsNeeded_592_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 592#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (d_w24.extractLsb' 0 32 == 480#32) = true
       then lsmpl.base 333 + 3348#64
       else lsmpl.base 333 + 604#64)
      s1
      (v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗ Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v2hs_check_ptsNeeded_592_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out d_w0 d_w8 d_w16 d_w24 d_w32 Rest
      hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx19_2, hx21_2, hx22_2, hx27_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx19_2,
       by simpa using hx21_2, by simpa using hx22_2, by simpa using hx27_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v2hs_check_ptsNeeded_592_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 592#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (d_w24.extractLsb' 0 32 == 480#32) = true
       then lsmpl.base 333 + 3348#64
       else lsmpl.base 333 + 604#64)
      s1
      (v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        Rest ∗ A.pool lim st s1)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
          Rest ∗ A.pool lim st s2) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v2hs_check_ptsNeeded_592_placed (ext := ext)
    s0 s1 out d_w0 d_w8 d_w16 d_w24 d_w32 (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

/-! ## `VmPreserved` & Pool-Threaded `uc` Validation Paths (`+3348 -> +4392 / +4660 / +4720 / +3436`) -/

theorem v2hs_uc_none_3348_to_4392_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4392#64) s1
      (v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
        noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v2hs_uc_none_3348_to_4392_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out d_w0 u16 u24 u32 u40 u48 u56 u64 u72 u80 Rest
      hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx19_2, hx22_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx19_2, by simpa using hx22_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v2hs_uc_none_3348_to_4392_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4392#64) s1
      (v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
        noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest ∗ A.pool lim st s1)
      (fun s2 P2 =>
        (P2 ⊢ v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          noneCap u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest ∗ A.pool lim st s2) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v2hs_uc_none_3348_to_4392_placed (ext := ext)
    s0 s1 out d_w0 u16 u24 u32 u40 u48 u56 u64 u72 u80 (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

theorem v2hs_validate_err_dk_3348_to_4660_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4660#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v2hs_validate_err_dk_3348_to_4660_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out d_w0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 Rest
      hsp0_align hu8 hdk
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx0_2, hx9_2, hx19_2, hx22_2, hx24_2, hx25_2, hx26_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx0_2, by simpa using hx9_2,
       by simpa using hx19_2, by simpa using hx22_2, by simpa using hx24_2,
       by simpa using hx25_2, by simpa using hx26_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v2hs_validate_err_dk_3348_to_4660_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4660#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest ∗ A.pool lim st s1)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗ Rest ∗ A.pool lim st s2) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v2hs_validate_err_dk_3348_to_4660_placed (ext := ext)
    s0 s1 out d_w0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 w96 w152 (Rest ∗ A.pool lim st s1)
    hsp0_align hu8 hdk hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

theorem v2hs_validate_err_auth_3348_to_4720_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4720#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v2hs_validate_err_auth_3348_to_4720_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out d_w0 u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 Rest
      hsp0_align hu8 hdk
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx9_2, hx19_2, hx22_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx9_2,
       by simpa using hx19_2, by simpa using hx22_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v2hs_validate_err_auth_3348_to_4720_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4720#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest ∗ A.pool lim st s1)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
            u8 u16 u24 noneCap u40 u48 u56 u64 u72 u80 ∗ Rest ∗ A.pool lim st s2) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = d_w0 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v2hs_validate_err_auth_3348_to_4720_placed (ext := ext)
    s0 s1 out d_w0 u8 u16 u24 u40 u48 u56 u64 u72 u80 w96 w152 (Rest ∗ A.pool lim st s1)
    hsp0_align hu8 hdk hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

theorem v2hs_validate_ok_3348_3436_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w200 w216 w224 w232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hu32 : u32.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3436#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        Rest)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 736 ∗
          Rest) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x8 = u72 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u48 ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        s2.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v2hs_validate_ok_3348_3436_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out d_w0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
      w96 w152 w176 w200 w216 w224 w232 Rest
      hsp0_align hu8 hdk hu32
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx22_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm
      ⟨hP2, hsp2, hx0_2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx0_2, by simpa using hx8_2,
       by simpa using hx9_2, by simpa using hx19_2, by simpa using hx20_2,
       by simpa using hx21_2, by simpa using hx22_2, by simpa using hx24_2,
       by simpa using hx25_2, by simpa using hx26_2, by simpa using hx27_2,
       by simpa using hx28_2, ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v2hs_validate_ok_3348_3436_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out d_w0 : BitVec 64)
    (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 : BitVec 64)
    (w96 w152 w176 w200 w216 w224 w232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hu8 : u8.toNat < 2 ^ 63)
    (hdk : (u24 == 2400#64) = true)
    (hu32 : u32.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 3348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d_w0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3436#64) s1
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ w96) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ w152) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ w176) ∗
        ((s0.sp - 2400#64 + 200#64) ↦₆₄ w200) ∗
        ((s0.sp - 2400#64 + 216#64) ↦₆₄ w216) ∗
        ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 656 ∗
        v2hs_ucWordsAt (s0.sp - 2400#64 + 896#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 ∗
        Rest ∗ A.pool lim st s1)
      (fun s2 P2 =>
        (P2 ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 200#64) ↦₆₄ u48) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ u40) ∗
          ((s0.sp - 2400#64 + 224#64) ↦₆₄ u80) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          memRegion (s0.sp - 2400#64 + 240#64) 736 ∗
          Rest ∗ A.pool lim st s2) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = u40 ∧
        s2.readReg64 .x8 = u72 ∧
        s2.readReg64 .x9 = u16 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x20 = u48 ∧
        s2.readReg64 .x21 = s1.readReg64 .x21 ∧
        s2.readReg64 .x22 = d_w0 ∧
        s2.readReg64 .x24 = u56 ∧
        s2.readReg64 .x25 = u64 ∧
        s2.readReg64 .x26 = u32 ∧
        s2.readReg64 .x27 = s1.readReg64 .x27 ∧
        s2.readReg64 .x28 = u80 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v2hs_validate_ok_3348_3436_placed (ext := ext)
    s0 s1 out d_w0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80
    w96 w152 w176 w200 w216 w224 w232 (Rest ∗ A.pool lim st s1)
    hsp0_align hu8 hdk hu32 hpc1 hrun1 hsp1 hx19_1 hx22_1 htr1
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨hP2, hvm, hrest⟩

/-! ## `VmPreserved` & Pool-Threaded `ekSent` Stack Assembly (`+8944 -> +9152 / +9036`) -/

theorem v2hs_assemble_ekSent_8944_9032_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (out d_w0 pa1 pa2 : BitVec 64)
    (u8 u16 u24 u48 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8944#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = pa1 >>> 8) (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (w0 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 9152#64
       else lsmpl.base 333 + 9036#64)
      s
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
          v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
          memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
          Rest) ∧
        VmPreserved s sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x9 = u24 ∧
        sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = u48 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = u80 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (CryptoVerification.SpqrV1.States.FromPb.v2hs_assemble_ekSent_8944_9032_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      out d_w0 pa1 pa2 u8 u16 u24 u48 u72 u80
      w0 w8 w16 w24 w32 w40 w48 Rest
      hsp0_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx22) (by simpa using hx23)
      (by simpa using hx25) (by simpa using hx26) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun sm Pm hvm
      ⟨hPm, hspm, hx0m, hx8m, hx9m, hx10m, hx19m, hx21m, hx22m, hx23m, hx25m, hx26m, hx27m, hx28m, htrm⟩ =>
      ⟨hPm, hvm, by simpa using hspm, by simpa using hx0m, by simpa using hx8m,
       by simpa using hx9m, by simpa using hx10m, by simpa using hx19m,
       by simpa using hx21m, by simpa using hx22m, by simpa using hx23m,
       by simpa using hx25m, by simpa using hx26m, by simpa using hx27m,
       by simpa using hx28m, ⟨by simpa using htrm.1, by simpa using htrm.2⟩⟩

theorem v2hs_assemble_ekSent_8944_9032_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (out d_w0 pa1 pa2 : BitVec 64)
    (u8 u16 u24 u48 u72 u80 : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8944#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = pa1) (hx25 : s.readReg64 .x25 = u48)
    (hx26 : s.readReg64 .x26 = pa1 >>> 8) (hx28 : s.readReg64 .x28 = u80)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (if (w0 + 1#64 == 0#64) = true
       then lsmpl.base 333 + 9152#64
       else lsmpl.base 333 + 9036#64)
      s
      (((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
        ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
        v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        Rest ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2400#64 + 96#64) ↦₆₄ u24) ∗
          ((s0.sp - 2400#64 + 152#64) ↦₆₄ u8) ∗
          ((s0.sp - 2400#64 + 176#64) ↦₆₄ u16) ∗
          ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
          ((s0.sp - 2400#64 + 232#64) ↦₆₄ u72) ∗
          v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 976#64) w0 w8 w16 w24 w32 w40 w48 ∗
          memRegion (s0.sp - 2400#64 + 1072#64) 192 ∗
          v2hs_ekSentWordsAt (s0.sp - 2400#64 + 1264#64) u48 pa1 u72 pa2 u8 u16 u24 u80 ∗
          memRegion (s0.sp - 2400#64 + 1344#64) 960 ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x0 = pa2 ∧
        sm.readReg64 .x8 = w0 ∧
        sm.readReg64 .x9 = u24 ∧
        sm.readReg64 .x10 = (s0.sp - 2400#64) + 1264#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = d_w0 ∧
        sm.readReg64 .x23 = pa1 ∧
        sm.readReg64 .x25 = u48 ∧
        sm.readReg64 .x26 = u8 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = u80 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hs_assemble_ekSent_8944_9032_placed (ext := ext)
    s0 s out d_w0 pa1 pa2 u8 u16 u24 u48 u72 u80
    w0 w8 w16 w24 w32 w40 w48 (Rest ∗ A.pool lim st s)
    hsp0_align hpc hrun hsp hx19 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsbPlacedBudgetAux
