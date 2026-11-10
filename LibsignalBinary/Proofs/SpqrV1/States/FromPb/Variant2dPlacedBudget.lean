/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 1 (`KeysSampled`) — Part D

Relocatable Block-`333` `sendingHdr` dispatch and staging (`+4016 -> +5860 | +4096`) with
`VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalPlacement blkLib_333 blkLib_eq_333 lsProg_333 lsmpl)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v1_optProtoPolyEncoderHeap v1_optProtoPolyEncoderWordsAt)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (checkBlockSafeVm isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)

theorem blk333_safeVm : checkBlockSafeVm blkLib_333.text = true := by decide +kernel

/-- `VmPreserved`-strengthened placed `sendingHdr = none` branch (`+4016 -> +5860`, Block `333`). -/
theorem v1_sendingHdr_none_4016_5860_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pa1 u8 u32 u72 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5860#64) s
      (((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = pa1 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlaced.v1_sendingHdr_none_4016_5860_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pa1 u8 u32 u72 Rest hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx26) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx0_1, hx19_1, hx21_1, hx22_1, hx28_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx0_1, by simpa using hx19_1,
       by simpa using hx21_1, by simpa using hx22_1, by simpa using hx28_1,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v1_sendingHdr_none_4016_5860_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pa1 u8 u32 u72 : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5860#64) s
      (((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 1496#64) ↦₆₄ noneCap) ∗ Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = pa1 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v1_sendingHdr_none_4016_5860_placed (ext := ext) s0 s fsp out pa1 u8 u32 u72
    (Rest ∗ A.pool lim st s) hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx26 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

/-- `VmPreserved`-strengthened placed `sendingHdr = some pbEnc` copy (`+4016 -> +4096`, Block `333`). -/
theorem v1_sendingHdr_some_copy_4016_4096_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA pa1 v200 u8 u32 u72 : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0 : w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4096#64) s
      (((fsp + 200#64) ↦₆₄ v200) ∗
        memRegion (fsp + 896#64) 56 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some pbEnc) w0 w8 w16 w24 w32 w40 w48 ∗
        Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 200#64) ↦₆₄ pa1) ∗
          protoPolynomialEncoderAt A (fsp + 896#64) pbEnc ∗
          memRegion (fsp + 1496#64) 56 ∗
          memRegion (pbA + 112#64) 56 ∗
          Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = fsp + 1888#64 ∧
        s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlaced.v1_sendingHdr_some_copy_4016_4096_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA pa1 v200 u8 u32 u72 pbEnc w0 w8 w16 w24 w32 w40 w48 Rest
      hfsp_align hw0 (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx25) (by simpa using hx26)
      (by simpa using hx27) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx28_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx0_1, by simpa using hx1_1,
       by simpa using hx19_1, by simpa using hx21_1, by simpa using hx22_1,
       by simpa using hx23_1, by simpa using hx25_1, by simpa using hx28_1,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v1_sendingHdr_some_copy_4016_4096_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA pa1 v200 u8 u32 u72 : BitVec 64)
    (pbEnc : ProtoPolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hw0 : w0.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4016#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = pa1 >>> 8)
    (hx21 : s.readReg64 .x21 = u8)
    (hx22 : s.readReg64 .x22 = u72)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64)
    (hx26 : s.readReg64 .x26 = pa1)
    (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = u32)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4096#64) s
      (((fsp + 200#64) ↦₆₄ v200) ∗
        memRegion (fsp + 896#64) 56 ∗
        v1_optProtoPolyEncoderWordsAt (fsp + 1496#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 112#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A.repAlloc (some pbEnc) w0 w8 w16 w24 w32 w40 w48 ∗
        Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 200#64) ↦₆₄ pa1) ∗
          protoPolynomialEncoderAt A.repAlloc (fsp + 896#64) pbEnc ∗
          memRegion (fsp + 1496#64) 56 ∗
          memRegion (pbA + 112#64) 56 ∗
          Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧
        s1.readReg64 .x0 = fsp + 1888#64 ∧
        s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x21 = u8 ∧
        s1.readReg64 .x22 = u72 ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧
        s1.readReg64 .x28 = u32 ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v1_sendingHdr_some_copy_4016_4096_placed (A := A.repAlloc) (ext := ext)
    s0 s fsp out pbA pa1 v200 u8 u32 u72 pbEnc w0 w8 w16 w24 w32 w40 w48
    (Rest ∗ A.pool lim st s) hfsp_align hw0 hpc hrun hsp
    hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
