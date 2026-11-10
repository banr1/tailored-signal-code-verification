/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0Placed
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 4 (`EkSentCt1Received`) — Part C0

Relocatable Block-`333` `<PolyDecoder>::from_pb` staging (`+2308..+2468`) and post-call
branches (`+2472 -> +8500 | +8180`) with `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement blkLib_333 blkLib_eq_333 lsProg_333 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (PolynomialError)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Poly (resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (loByte unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v4b_optProtoPolyDecoderWordsAt v4b_optProtoUcWordsAt
   v4c_DecWords v4c_ct1Len_x27 v4c_decWordsAt v4c_destStackSlots v4c_ucSpillSlots)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (checkBlockSafeVm isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)

private theorem blk333_safeVm : checkBlockSafeVm blkLib_333.text = true := by decide +kernel

@[local simp] private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

/-- `VmPreserved`-strengthened segment `+2308..+2468 -> lsmpl.base 376` (`decoderFromPb`). -/
theorem v4c_step_2308_ok_some_to_35448_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64)
    (s896 s904 s912 : BitVec 64) (s920 s924 : BitVec 32) (s928 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx23 : s.readReg64 .x23 = d24.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s
      (v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
        ((fsp + 224#64) ↦₆₄ d32) ∗
        ((fsp + 232#64) ↦₃₂ d28) ∗
        v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) s896 s904 s912 s920 s924 s928 ∗
        v4b_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4c_ucSpillSlots fsp
            ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗
          ((fsp + 232#64) ↦₃₂ d28) ∗
          v4b_optProtoPolyDecoderWordsAt (fsp + 896#64)
            d0 d8 d16 d24 d28 d32 ∗
          v4b_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
          Frame) ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = fsp + 1888#64 ∧
        s'.readReg64 .x1 = fsp + 896#64 ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64 ∧
        s'.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64 ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x23 = fsp + 1888#64 ∧
        s'.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64 ∧
        s'.readReg64 .x25 = rkLen ∧
        s'.readReg64 .x26 = rkPtr ∧
        s'.readReg64 .x27 = fsp + 1792#64 ∧
        s'.readReg64 .x30 = lsmpl.base 333 + 2472#64 ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4c_step_2308_ok_some_to_35448_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out d0 d8 d16 d32 d24 d28
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch
      v32 v40 v48 v56 v72 v80 v128 v136 v144 v216
      s896 s904 s912 s920 s924 s928 Frame
      hfsp_align hrk_lt hd0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx23)
      (by simpa using hx24) (by simpa using hx28))
    fun s' P' hvm ⟨hP', hsp', hx0, hx1, hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27', hx30', htr'⟩ =>
      ⟨hP', hvm, by simpa using hsp', by simpa using hx0, by simpa using hx1,
       by simpa using hx19', by simpa using hx20', by simpa using hx21', by simpa using hx22',
       by simpa using hx23', by simpa using hx24', by simpa using hx25', by simpa using hx26',
       by simpa using hx27', by simpa using hx30',
       ⟨by simpa using htr'.1, by simpa using htr'.2⟩⟩

theorem v4c_step_2308_ok_some_to_35448_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 : BitVec 64)
    (s896 s904 s912 : BitVec 64) (s920 s924 : BitVec 32) (s928 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hd0_lt : d0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2308#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = d16)
    (hx23 : s.readReg64 .x23 = d24.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = d8)
    (hx28 : s.readReg64 .x28 = d0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s
      (v4c_ucSpillSlots fsp v32 v40 v48 v56 v72 v80 v128 v136 v144 v216 ∗
        ((fsp + 224#64) ↦₆₄ d32) ∗
        ((fsp + 232#64) ↦₃₂ d28) ∗
        v4b_optProtoPolyDecoderWordsAt (fsp + 896#64) s896 s904 s912 s920 s924 s928 ∗
        v4b_optProtoUcWordsAt (fsp + 1888#64)
          rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ v4c_ucSpillSlots fsp
            ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗
          ((fsp + 232#64) ↦₃₂ d28) ∗
          v4b_optProtoPolyDecoderWordsAt (fsp + 896#64)
            d0 d8 d16 d24 d28 d32 ∗
          v4b_optProtoUcWordsAt (fsp + 1888#64)
            rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = fsp + 1888#64 ∧
        s'.readReg64 .x1 = fsp + 896#64 ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64 ∧
        s'.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64 ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x23 = fsp + 1888#64 ∧
        s'.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64 ∧
        s'.readReg64 .x25 = rkLen ∧
        s'.readReg64 .x26 = rkPtr ∧
        s'.readReg64 .x27 = fsp + 1792#64 ∧
        s'.readReg64 .x30 = lsmpl.base 333 + 2472#64 ∧
        TraceCalleeSaved s' s) := by
  have hwp := v4c_step_2308_ok_some_to_35448_placed (ext := ext)
    s fsp out d0 d8 d16 d32 d24 d28
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch
    v32 v40 v48 v56 v72 v80 v128 v136 v144 v216
    s896 s904 s912 s920 s924 s928 (Frame ∗ A.pool lim st s)
    hfsp_align hrk_lt hd0_lt hpc hrun hsp hx19 hx20 hx23 hx24 hx28
  refine SepWP.mono hwp fun s' P' _ _ ⟨hP', hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, hrest⟩

/-- `VmPreserved`-strengthened segment `+2472..+2480 -> +8500` when `decoderFromPb` returns `.error e`. -/
theorem v4c_step_2472_err_to_8500_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s : State) (fsp out dkCap rkPtr : BitVec 64)
    (e : PolynomialError)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8500#64) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error e) ∗ Frame)
      (fun s' P' =>
        (P' ⊢ memRegion (fsp + 1888#64) 400 ∗ Frame) ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x26 = rkPtr ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4c_step_2472_err_to_8500_placed
      (A := A) (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out dkCap rkPtr e Frame hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx22) (by simpa using hx26))
    fun s' P' hvm ⟨hP', hsp', hx19', hx22', hx26', htr'⟩ =>
      ⟨hP', hvm, by simpa using hsp', by simpa using hx19',
       by simpa using hx22', by simpa using hx26',
       ⟨by simpa using htr'.1, by simpa using htr'.2⟩⟩

theorem v4c_step_2472_err_to_8500_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out dkCap rkPtr : BitVec 64)
    (e : PolynomialError)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 2472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8500#64) s
      (resultPolyDecoderFromPbAt A.repAlloc (fsp + 1888#64) (.error e) ∗ Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ memRegion (fsp + 1888#64) 400 ∗ Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x22 = dkCap ∧
        s'.readReg64 .x26 = rkPtr ∧
        TraceCalleeSaved s' s) := by
  have hwp := v4c_step_2472_err_to_8500_placed (A := A.repAlloc) (ext := ext)
    s fsp out dkCap rkPtr e (Frame ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx19 hx22 hx26
  refine SepWP.mono hwp fun s' P' _ _ ⟨hP', hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, hrest⟩

/-- `VmPreserved`-strengthened segment `+2472..+2764 -> +8180` when `decoderFromPb` returns `.ok dec`. -/
theorem v4c_step_2472_ok_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (dw : v4c_DecWords)
    (w160 : BitVec 64) (d172 : BitVec 32) (w192 w208 w224 w232 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : dw.g0.w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx23 : s.readReg64 .x23 = fsp + 1888#64)
    (hx24 : s.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = rkLen)
    (hx26 : s.readReg64 .x26 = rkPtr)
    (hx27 : s.readReg64 .x27 = fsp + 1792#64) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (v4c_ucSpillSlots fsp
          ((ct1Len.extractLsb' 0 8).zeroExtend 64)
          mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
        v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
          q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
          w832 q848 w864 w880 w888 ∗
        v4c_decWordsAt (fsp + 1888#64) dw ∗
        Frame)
      (fun s' P' =>
        (P' ⊢ v4c_ucSpillSlots fsp
            ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          v4c_destStackSlots fsp
            dw.g3.u336 ((loByte dw.g0.u32).zeroExtend 32) dw.g4.u384 rkPtr dw.g4.u368 dw.g3.u320
            dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
            dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
            dw.g3.u280
            (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
            (dw.g0.u48 >>> 8)
            (unshiftWord dw.g0.u8 (loByte dw.g0.w16))
            (dw.g0.w16 >>> 8) ∗
          v4c_decWordsAt (fsp + 1888#64) dw ∗
          Frame) ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = ct1Ptr ∧
        s'.readReg64 .x1 = dw.g4.u360 ∧
        s'.readReg64 .x2 = dw.g3.u288 ∧
        s'.readReg32 .x3 = ((ct1Len.extractLsb' 0 8).zeroExtend 64).setWidth 32 ∧
        s'.readReg64 .x4 = epoch ∧
        s'.readReg64 .x5 = dw.g0.w0 ∧
        s'.readReg64 .x6 = fsp + 576#64 ∧
        s'.readReg64 .x7 = dw.g0.u24 ∧
        s'.readReg64 .x8 = 6#64 ∧
        s'.readReg64 .x9 = dkCap ∧
        s'.readReg64 .x10 = dw.g3.u328 ∧
        s'.readReg64 .x11 = dw.g3.u296 ∧
        s'.readReg64 .x12 = dw.g4.u352 ∧
        s'.readReg64 .x13 = mkCap ∧
        s'.readReg64 .x14 = dkPtr ∧
        s'.readReg64 .x15 = rkCap ∧
        s'.readReg64 .x16 = dw.g4.u392 ∧
        s'.readReg64 .x17 = ct1Cap ∧
        s'.readReg64 .x18 = dkLen ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = rkLen ∧
        s'.readReg32 .x21 = (loByte dw.g0.u8).zeroExtend 32 ∧
        s'.readReg64 .x22 = dw.g3.u304 ∧
        s'.readReg64 .x23 = fsp + 848#64 ∧
        s'.readReg64 .x24 = dw.g3.u312 ∧
        s'.readReg64 .x25 = mkPtr ∧
        s'.readReg64 .x26 = dw.g4.u344 ∧
        s'.readReg64 .x27 = v4c_ct1Len_x27 ct1Len ∧
        s'.readReg64 .x28 = dw.g4.u376 ∧
        s'.readReg64 .x30 = mkLen ∧
        TraceCalleeSaved s' s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.v4c_step_2472_ok_to_8180_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch
      dw w160 d172 w192 w208 w224 w232
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 Frame
      hfsp_align hw0_lt
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx23) (by simpa using hx24)
      (by simpa using hx25) (by simpa using hx26) (by simpa using hx27))
    fun s' P' hvm ⟨hP', hsp', hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
      hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17,
      hx18, hx19', hx20', hx21', hx22', hx23', hx24', hx25', hx26', hx27',
      hx28', hx30', htr'⟩ =>
      ⟨hP', hvm, by simpa using hsp', by simpa using hx0, by simpa using hx1,
       by simpa using hx2, by simpa using hx3, by simpa using hx4, by simpa using hx5,
       by simpa using hx6, by simpa using hx7, by simpa using hx8, by simpa using hx9,
       by simpa using hx10, by simpa using hx11, by simpa using hx12, by simpa using hx13,
       by simpa using hx14, by simpa using hx15, by simpa using hx16, by simpa using hx17,
       by simpa using hx18, by simpa using hx19', by simpa using hx20', by simpa using hx21',
       by simpa using hx22', by simpa using hx23', by simpa using hx24', by simpa using hx25',
       by simpa using hx26', by simpa using hx27', by simpa using hx28', by simpa using hx30',
       ⟨by simpa using htr'.1, by simpa using htr'.2⟩⟩

theorem v4c_step_2472_ok_to_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch : BitVec 64)
    (dw : v4c_DecWords)
    (w160 : BitVec 64) (d172 : BitVec 32) (w192 w208 w224 w232 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0_lt : dw.g0.w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 2472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx23 : s.readReg64 .x23 = fsp + 1888#64)
    (hx24 : s.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = rkLen)
    (hx26 : s.readReg64 .x26 = rkPtr)
    (hx27 : s.readReg64 .x27 = fsp + 1792#64) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (v4c_ucSpillSlots fsp
          ((ct1Len.extractLsb' 0 8).zeroExtend 64)
          mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
        v4c_destStackSlots fsp w160 d172 w192 w208 w224 w232
          q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
          w832 q848 w864 w880 w888 ∗
        v4c_decWordsAt (fsp + 1888#64) dw ∗
        Frame ∗ A.pool lim st s)
      (fun s' P' =>
        (P' ⊢ v4c_ucSpillSlots fsp
            ((ct1Len.extractLsb' 0 8).zeroExtend 64)
            mkLen epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
          v4c_destStackSlots fsp
            dw.g3.u336 ((loByte dw.g0.u32).zeroExtend 32) dw.g4.u384 rkPtr dw.g4.u368 dw.g3.u320
            dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
            dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
            dw.g3.u280
            (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
            (dw.g0.u48 >>> 8)
            (unshiftWord dw.g0.u8 (loByte dw.g0.w16))
            (dw.g0.w16 >>> 8) ∗
          v4c_decWordsAt (fsp + 1888#64) dw ∗
          Frame ∗ A.pool lim st s') ∧
        VmPreserved s s' ∧
        s'.sp = fsp ∧
        s'.readReg64 .x0 = ct1Ptr ∧
        s'.readReg64 .x1 = dw.g4.u360 ∧
        s'.readReg64 .x2 = dw.g3.u288 ∧
        s'.readReg32 .x3 = ((ct1Len.extractLsb' 0 8).zeroExtend 64).setWidth 32 ∧
        s'.readReg64 .x4 = epoch ∧
        s'.readReg64 .x5 = dw.g0.w0 ∧
        s'.readReg64 .x6 = fsp + 576#64 ∧
        s'.readReg64 .x7 = dw.g0.u24 ∧
        s'.readReg64 .x8 = 6#64 ∧
        s'.readReg64 .x9 = dkCap ∧
        s'.readReg64 .x10 = dw.g3.u328 ∧
        s'.readReg64 .x11 = dw.g3.u296 ∧
        s'.readReg64 .x12 = dw.g4.u352 ∧
        s'.readReg64 .x13 = mkCap ∧
        s'.readReg64 .x14 = dkPtr ∧
        s'.readReg64 .x15 = rkCap ∧
        s'.readReg64 .x16 = dw.g4.u392 ∧
        s'.readReg64 .x17 = ct1Cap ∧
        s'.readReg64 .x18 = dkLen ∧
        s'.readReg64 .x19 = out ∧
        s'.readReg64 .x20 = rkLen ∧
        s'.readReg32 .x21 = (loByte dw.g0.u8).zeroExtend 32 ∧
        s'.readReg64 .x22 = dw.g3.u304 ∧
        s'.readReg64 .x23 = fsp + 848#64 ∧
        s'.readReg64 .x24 = dw.g3.u312 ∧
        s'.readReg64 .x25 = mkPtr ∧
        s'.readReg64 .x26 = dw.g4.u344 ∧
        s'.readReg64 .x27 = v4c_ct1Len_x27 ct1Len ∧
        s'.readReg64 .x28 = dw.g4.u376 ∧
        s'.readReg64 .x30 = mkLen ∧
        TraceCalleeSaved s' s) := by
  have hwp := v4c_step_2472_ok_to_8180_placed (ext := ext)
    s fsp out rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len epoch
    dw w160 d172 w192 w208 w224 w232
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888 (Frame ∗ A.pool lim st s)
    hfsp_align hw0_lt hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
  refine SepWP.mono hwp fun s' P' _ _ ⟨hP', hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP'
  exact ⟨hP', hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0PlacedBudget
