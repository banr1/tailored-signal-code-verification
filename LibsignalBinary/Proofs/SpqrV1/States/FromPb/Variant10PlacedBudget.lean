/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Variant 10 (`Ct2Sampled`, `+1632`) — Encoder Dispatch

Proves `VmPreserved`-strengthened and `RustCliAllocBudget M` pool-threading Block `333` steps for
Variant 10 (`+1632 -> +1720`, `+5728 -> +7212`, `+5728 -> lsmpl.base 374 -> +5808`, `+5808 -> +5820`,
and `+5808 -> +7904`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10PlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 lsProg_333 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Poly
  (polyEncoderSize protoPolynomialEncoderAt protoPolynomialEncoderSize resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
  (EncoderFromPbGhost encoderFromPbStack fromPbResult loByte loBytes7)
open CryptoVerification.SpqrV1.States.FromPb (TraceCalleeSaved)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
  (EncoderFromPbAllocEnv EncoderFromPbEnv encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget encoder_from_pb_ok_of_alloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

/-! ## 0. Subroutine Bridges for `<PolyEncoder>::from_pb` (Block `374`) on `lsProg_333` -/

/-- Budget-threaded subroutine contract for `<PolyEncoder>::from_pb` (Block `374`) on `lsProg_333`. -/
theorem v10_sub_ok_encoder_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  hEnc

/-- Discharge `v10_sub_ok_encoder_from_pb_placed` unconditionally from `FromPbAllocHooksBudget`. -/
theorem v10_sub_ok_encoder_from_pb_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  encoder_from_pb_ok_of_alloc_placed hA

/-! ## 1. `+1632 -> +1720`: Loading `Authenticator` PB and `epoch` -/

/-- `VmPreserved`-strengthened `+1632 -> +1720` load step in Block `333`. -/
theorem v10_ct2Sent_load_1632_to_1720_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA cap_enc c1 p1 l1 c2 p2 l2 ep v152 v200 v232 : BitVec 64)
    (b16 : BitVec 8) (v224 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1720#64) s1
      (((pbA + 8#64) ↦₆₄ cap_enc) ∗
        ((pbA + 16#64) ↦₈ b16) ∗
        ((pbA + 64#64) ↦₆₄ c1) ∗
        ((pbA + 72#64) ↦₆₄ p1) ∗
        ((pbA + 80#64) ↦₆₄ l1) ∗
        ((pbA + 88#64) ↦₆₄ c2) ∗
        ((pbA + 96#64) ↦₆₄ p2) ∗
        ((pbA + 104#64) ↦₆₄ l2) ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗
        (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((pbA + 8#64) ↦₆₄ cap_enc) ∗
          ((pbA + 16#64) ↦₈ b16) ∗
          ((pbA + 64#64) ↦₆₄ c1) ∗
          ((pbA + 72#64) ↦₆₄ p1) ∗
          ((pbA + 80#64) ↦₆₄ l1) ∗
          ((pbA + 88#64) ↦₆₄ c2) ∗
          ((pbA + 96#64) ↦₆₄ p2) ∗
          ((pbA + 104#64) ↦₆₄ l2) ∗
          ((pbA + 112#64) ↦₆₄ ep) ∗
          (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = l1 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v10_ct2Sent_load_1632_to_1720_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA cap_enc c1 p1 l1 c2 p2 l2 ep v152 v200 v232 b16 v224 Rest
      hsp0_align hc1_lt
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx19_m, hx20_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m, by simpa using hx20_m,
       by simpa using hx22_m, by simpa using hx23_m, by simpa using hx24_m,
       by simpa using hx25_m, by simpa using hx26_m, by simpa using hx27_m,
       by simpa using hx28_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v10_ct2Sent_load_1632_to_1720_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA cap_enc c1 p1 l1 c2 p2 l2 ep v152 v200 v232 : BitVec 64)
    (b16 : BitVec 8) (v224 : BitVec 32) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hc1_lt : c1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1632#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1720#64) s1
      (((pbA + 8#64) ↦₆₄ cap_enc) ∗
        ((pbA + 16#64) ↦₈ b16) ∗
        ((pbA + 64#64) ↦₆₄ c1) ∗
        ((pbA + 72#64) ↦₆₄ p1) ∗
        ((pbA + 80#64) ↦₆₄ l1) ∗
        ((pbA + 88#64) ↦₆₄ c2) ∗
        ((pbA + 96#64) ↦₆₄ p2) ∗
        ((pbA + 104#64) ↦₆₄ l2) ∗
        ((pbA + 112#64) ↦₆₄ ep) ∗
        (((s0.sp - 2400#64) + 152#64) ↦₆₄ v152) ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ v200) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₃₂ v224) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ v232) ∗
        Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          ((pbA + 8#64) ↦₆₄ cap_enc) ∗
          ((pbA + 16#64) ↦₈ b16) ∗
          ((pbA + 64#64) ↦₆₄ c1) ∗
          ((pbA + 72#64) ↦₆₄ p1) ∗
          ((pbA + 80#64) ↦₆₄ l1) ∗
          ((pbA + 88#64) ↦₆₄ c2) ∗
          ((pbA + 96#64) ↦₆₄ p2) ∗
          ((pbA + 104#64) ↦₆₄ l2) ∗
          ((pbA + 112#64) ↦₆₄ ep) ∗
          (((s0.sp - 2400#64) + 152#64) ↦₆₄ ep) ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗
          (((s0.sp - 2400#64) + 224#64) ↦₃₂ b16.zeroExtend 32) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ p2) ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = p1 ∧
        sm.readReg64 .x22 = cap_enc ∧
        sm.readReg64 .x23 = pbA + 8#64 ∧
        sm.readReg64 .x24 = c1 ∧
        sm.readReg64 .x25 = c2 ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = l1 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v10_ct2Sent_load_1632_to_1720_placed (ext := ext)
    s0 s1 out pbA cap_enc c1 p1 l1 c2 p2 l2 ep v152 v200 v232 b16 v224
    (Rest ∗ A.pool lim st s1)
    hsp0_align hc1_lt hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## 2. `+5728 -> +7212`: `sending_ct2 = none` Branch -/

/-- `VmPreserved`-strengthened `+5728 -> +7212` `sending_ct2 = none` branch in Block `333`. -/
theorem v10_ct2Sent_5728_to_7212_none_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa1 l1 l2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 5728#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx22_1 : s1.readReg64 .x22 = noneCap)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7212#64) s1
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x26 = l2 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v10_ct2Sent_5728_to_7212_none_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pa1 l1 l2 Rest
      hsp0_align hl1_lt
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx26_1) ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, hx26_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       by simpa using hx21_m, by simpa using hx26_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v10_ct2Sent_5728_to_7212_none_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa1 l1 l2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 5728#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx22_1 : s1.readReg64 .x22 = noneCap)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7212#64) s1
      ((((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗ Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 200#64) ↦₆₄ l1) ∗ Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x26 = l2 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v10_ct2Sent_5728_to_7212_none_placed (ext := ext)
    s0 s1 out pa1 l1 l2 (Rest ∗ A.pool lim st s1)
    hsp0_align hl1_lt hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx26_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-! ## 3. `+5728 -> lsmpl.base 374 -> +5808`: Copying `ProtoPolynomialEncoder` and Calling `<PolyEncoder>::from_pb` -/

/-- `VmPreserved`-strengthened `+5728 -> lsmpl.base 374` copy-and-`bl` step in Block `333`. -/
theorem v10_ct2Sent_copy_to_encoder_call_5728_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State)
    (fsp out pbA pa1 l1 l2 cap_pts ptr_pts len_pts cap_polys ptr_polys len_polys w56 : BitVec 64)
    (u1392 u1401 u1409 u1417 u1424 u1432 u1440 : BitVec 64) (b1400 : BitVec 8)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hcap_pts_lt : cap_pts.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 5728#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx22_1 : s1.readReg64 .x22 = cap_pts)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1
      (((fsp + 200#64) ↦₆₄ l1) ∗
        ((fsp + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
        ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
        ((pbA + 24#64) ↦₆₄ len_pts) ∗
        ((pbA + 32#64) ↦₆₄ cap_polys) ∗
        ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
        ((pbA + 48#64) ↦₆₄ len_polys) ∗
        ((pbA + 56#64) ↦₆₄ w56) ∗
        ((fsp + 1392#64) ↦₆₄ u1392) ∗
        ((fsp + 1400#64) ↦₈ b1400) ∗
        ((fsp + 1401#64) ↦₆₄ u1401) ∗
        ((fsp + 1409#64) ↦₆₄ u1409) ∗
        ((fsp + 1417#64) ↦ₛ loBytes7 u1417) ∗
        ((fsp + 1424#64) ↦₆₄ u1424) ∗
        ((fsp + 1432#64) ↦₆₄ u1432) ∗
        ((fsp + 1440#64) ↦₆₄ u1440) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 200#64) ↦₆₄ l1) ∗
          ((fsp + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
          ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
          ((pbA + 24#64) ↦₆₄ len_pts) ∗
          ((pbA + 32#64) ↦₆₄ cap_polys) ∗
          ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
          ((pbA + 48#64) ↦₆₄ len_polys) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗
          ((fsp + 1392#64) ↦₆₄ cap_pts) ∗
          ((fsp + 1400#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 1408#64) ↦₆₄ len_pts) ∗
          ((fsp + 1416#64) ↦₆₄ cap_polys) ∗
          ((fsp + 1424#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 1432#64) ↦₆₄ len_polys) ∗
          ((fsp + 1440#64) ↦₆₄ w56) ∗
          Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x22 = cap_pts ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 5808#64 ∧
        TraceCalleeSaved sm s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v10_ct2Sent_copy_to_encoder_call_5728_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out pbA pa1 l1 l2 cap_pts ptr_pts len_pts cap_polys ptr_polys len_polys w56
      u1392 u1401 u1409 u1417 u1424 u1432 u1440 b1400 Rest
      hfsp_align hl1_lt hcap_pts_lt
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx22_1)
      (by simpa using hx26_1) (by simpa using hx27_1))
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx26_m, hx27_m, hx29_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx26_m, by simpa using hx27_m, by simpa using hx29_m,
       by simpa using hx30_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v10_ct2Sent_copy_to_encoder_call_5728_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s1 : State)
    (fsp out pbA pa1 l1 l2 cap_pts ptr_pts len_pts cap_polys ptr_polys len_polys w56 : BitVec 64)
    (u1392 u1401 u1409 u1417 u1424 u1432 u1440 : BitVec 64) (b1400 : BitVec 8)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hl1_lt : l1.toNat < 2 ^ 63)
    (hcap_pts_lt : cap_pts.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 5728#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx22_1 : s1.readReg64 .x22 = cap_pts)
    (hx26_1 : s1.readReg64 .x26 = l2)
    (hx27_1 : s1.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1
      (((fsp + 200#64) ↦₆₄ l1) ∗
        ((fsp + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
        ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
        ((pbA + 24#64) ↦₆₄ len_pts) ∗
        ((pbA + 32#64) ↦₆₄ cap_polys) ∗
        ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
        ((pbA + 48#64) ↦₆₄ len_polys) ∗
        ((pbA + 56#64) ↦₆₄ w56) ∗
        ((fsp + 1392#64) ↦₆₄ u1392) ∗
        ((fsp + 1400#64) ↦₈ b1400) ∗
        ((fsp + 1401#64) ↦₆₄ u1401) ∗
        ((fsp + 1409#64) ↦₆₄ u1409) ∗
        ((fsp + 1417#64) ↦ₛ loBytes7 u1417) ∗
        ((fsp + 1424#64) ↦₆₄ u1424) ∗
        ((fsp + 1432#64) ↦₆₄ u1432) ∗
        ((fsp + 1440#64) ↦₆₄ u1440) ∗
        Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 200#64) ↦₆₄ l1) ∗
          ((fsp + 224#64) ↦₃₂ (loByte ptr_pts).zeroExtend 32) ∗
          ((pbA + 16#64) ↦₆₄ ptr_pts) ∗
          ((pbA + 24#64) ↦₆₄ len_pts) ∗
          ((pbA + 32#64) ↦₆₄ cap_polys) ∗
          ((pbA + 40#64) ↦₆₄ ptr_polys) ∗
          ((pbA + 48#64) ↦₆₄ len_polys) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗
          ((fsp + 1392#64) ↦₆₄ cap_pts) ∗
          ((fsp + 1400#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 1408#64) ↦₆₄ len_pts) ∗
          ((fsp + 1416#64) ↦₆₄ cap_polys) ∗
          ((fsp + 1424#64) ↦₆₄ ptr_polys) ∗
          ((fsp + 1432#64) ↦₆₄ len_polys) ∗
          ((fsp + 1440#64) ↦₆₄ w56) ∗
          Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1392#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x22 = cap_pts ∧
        sm.readReg64 .x26 = l2 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 5808#64 ∧
        TraceCalleeSaved sm s1) := by
  have hwp := v10_ct2Sent_copy_to_encoder_call_5728_placed (ext := ext)
    s1 fsp out pbA pa1 l1 l2 cap_pts ptr_pts len_pts cap_polys ptr_polys len_polys w56
    u1392 u1401 u1409 u1417 u1424 u1432 u1440 b1400 (Rest ∗ A.pool lim st s1)
    hfsp_align hl1_lt hcap_pts_lt hpc1 hrun1 hsp1 hx19_1 hx21_1 hx22_1 hx26_1 hx27_1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- Total-correctness (`SepWP`) `<PolyEncoder>::from_pb` call step (`lsmpl.base 374 -> +5808`)
    on `lsProg_333` under `FitsEnv M lim st (EncoderFromPbAllocEnv pb)`. -/
theorem v10_ct2Sent_call_encoder_374_to_5808_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hEnc : EncoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ) (s0 s3 : State) (fsp : BitVec 64)
    (pb : ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hpts : ∀ bs ∈ pb.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pb))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 374)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx0_3 : s3.readReg64 .x0 = fsp + 1888#64)
    (hx1_3 : s3.readReg64 .x1 = fsp + 1392#64)
    (hx30_3 : s3.readReg64 .x30 = lsmpl.base 333 + 5808#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5808#64) s3
      ((memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1392#64) pb ∗
        A.pool lim st s3 ∗
        stackAt fsp encoderFromPbStack) ∗
       Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv pb evs ∧
          (Pm ⊢
            resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pb) ∗
            memRegion (fsp + 1392#64) protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp encoderFromPbStack ∗
            Rest) ∧
          sm.sp = fsp ∧
          CalleeSavedPreserved s3 sm ∧
          sm.readReg64 .x19 = s3.readReg64 .x19 ∧
          sm.readReg64 .x21 = s3.readReg64 .x21 ∧
          sm.readReg64 .x26 = s3.readReg64 .x26 ∧
          TraceCalleeSaved sm s0) := by
  have hsp3_align : s3.spAligned = true := by
    change (s3.sp &&& 15#64 == 0#64) = true
    rw [hsp3]
    exact hfsp_align
  have hpre_ent :
      (memRegion (fsp + 1888#64) polyEncoderSize ∗
       protoPolynomialEncoderAt A.repAlloc (fsp + 1392#64) pb ∗
       A.pool lim st s3 ∗
       stackAt fsp encoderFromPbStack) ⊢
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)).pre
        (⟨fsp + 1888#64, fsp + 1392#64, pb⟩, st) s3 := by
    dsimp only [withLsCodeLoaded, encoderFromPbSpec]
    rw [hsp3, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s3.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hcl3 (Entails.pure_right ⟨hx0_3, hx1_3, hpts, hfits,
      by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .x30); rw [show s3.readReg64 .x30 = _ from hx30_3]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.call_subroutine_frame hEnc
    (x := (⟨fsp + 1888#64, fsp + 1392#64, pb⟩, st))
    (F := Rest)
    hpc3 hrun3 hsp3_align hx30_3
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
    (fun _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    ?_
    (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm))
  intro sm hpcm hrunm hspm hcsm
  have hcsm' := hcsm
  rcases hcsm with ⟨hx19_f, _, hx21_f, _, _, _, _, hx26_f, _, _, _, hvregs_f⟩
  dsimp only [withLsCodeLoaded, encoderFromPbSpec]
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_elim; intro evs
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr_f, _hacp_f, henv⟩
  apply ProofLib.SepWP.done hpcm hrunm
  refine ⟨evs, henv, ?_, hspm.trans hsp3, hcsm', hx19_f, hx21_f, hx26_f,
    ⟨htr_f.trans htr3.1, hvregs_f.trans htr3.2⟩⟩
  rw [hsp3]
  exact Entails.of_eq (by sep_ac_rfl)

theorem v10_ct2Sent_call_encoder_374_to_5808_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (st : M.σ) (s0 s3 : State) (fsp : BitVec 64)
    (pb : ProtoPolynomialEncoder) (Rest : SepProp)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hpts : ∀ bs ∈ pb.pts, bs.length ≤ 2 * 0x0555555555555555)
    (hfits : FitsEnv M lim st (EncoderFromPbAllocEnv pb))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = lsmpl.base 374)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx0_3 : s3.readReg64 .x0 = fsp + 1888#64)
    (hx1_3 : s3.readReg64 .x1 = fsp + 1392#64)
    (hx30_3 : s3.readReg64 .x30 = lsmpl.base 333 + 5808#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5808#64) s3
      ((memRegion (fsp + 1888#64) polyEncoderSize ∗
        protoPolynomialEncoderAt A.repAlloc (fsp + 1392#64) pb ∗
        A.pool lim st s3 ∗
        stackAt fsp encoderFromPbStack) ∗
       Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          EncoderFromPbEnv pb evs ∧
          (Pm ⊢
            resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (fromPbResult pb) ∗
            memRegion (fsp + 1392#64) protoPolynomialEncoderSize ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt fsp encoderFromPbStack ∗
            Rest) ∧
          sm.sp = fsp ∧
          CalleeSavedPreserved s3 sm ∧
          sm.readReg64 .x19 = s3.readReg64 .x19 ∧
          sm.readReg64 .x21 = s3.readReg64 .x21 ∧
          sm.readReg64 .x26 = s3.readReg64 .x26 ∧
          TraceCalleeSaved sm s0) :=
  v10_ct2Sent_call_encoder_374_to_5808_placed
    (encoder_from_pb_ok_of_alloc_placed hA)
    st s0 s3 fsp pb Rest hcl3 hpts hfits hfsp_align hpc3 hrun3 hsp3 hx0_3 hx1_3 hx30_3 htr3

/-! ## 4. Post-`<PolyEncoder>::from_pb` Error and Ok Branches (`+5808 -> +5820` and `+5808 -> +7904`) -/

/-- `VmPreserved`-strengthened `+5808 -> +5820` post-encoder `Err` branch in Block `333`. -/
theorem v10_ct2Sent_5808_to_5820_err_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa1 ca2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5808#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5820#64) s1
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x26 = ca2 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v10_ct2Sent_5808_to_5820_err_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pa1 ca2 Rest
      hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1) (by simpa using hx26_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, hx26_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       by simpa using hx21_m, by simpa using hx26_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v10_ct2Sent_5808_to_5820_err_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pa1 ca2 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 5808#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = pa1)
    (hx26_1 : s1.readReg64 .x26 = ca2)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5820#64) s1
      ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = pa1 ∧
        sm.readReg64 .x26 = ca2 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v10_ct2Sent_5808_to_5820_err_placed (ext := ext)
    s0 s1 out pa1 ca2 (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened `+5808 -> +7904` post-encoder `Ok` branch in Block `333`. -/
theorem v10_ct2Sent_5808_to_7904_ok_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp : BitVec 64)
    (tag : BitVec 64) (htag : tag = 0#64 ∨ tag = 1#64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 5808#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7904#64) s
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest) ∧
        VmPreserved s s2 ∧
        s2.sp = fsp ∧
        s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x19 = s.readReg64 .x19 ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.v10_ct2Sent_5808_to_7904_ok_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp tag htag Rest
      hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx15_2, hx19_2, hx21_2, hx26_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx15_2, by simpa using hx19_2,
       by simpa using hx21_2, by simpa using hx26_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v10_ct2Sent_5808_to_7904_ok_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp : BitVec 64)
    (tag : BitVec 64) (htag : tag = 0#64 ∨ tag = 1#64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 5808#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7904#64) s
      (((fsp + 1888#64) ↦₆₄ tag) ∗ Rest ∗ A.pool lim st s)
      (fun s2 P2 =>
        (P2 ⊢ ((fsp + 1888#64) ↦₆₄ tag) ∗ Rest ∗ A.pool lim st s2) ∧
        VmPreserved s s2 ∧
        s2.sp = fsp ∧
        s2.readReg64 .x15 = tag ∧
        s2.readReg64 .x19 = s.readReg64 .x19 ∧
        s2.readReg64 .x21 = s.readReg64 .x21 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v10_ct2Sent_5808_to_7904_ok_placed (ext := ext)
    s0 s fsp tag htag (Rest ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp htr
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hP2
  exact ⟨Entails.trans hP2 (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10PlacedBudget
