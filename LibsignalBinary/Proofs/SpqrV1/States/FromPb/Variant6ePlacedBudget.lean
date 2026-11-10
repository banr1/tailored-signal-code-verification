/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlaced
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part E

Lifts the Variant 6 `<PolyDecoder>::from_pb` call and branch steps (`+9936 -> +10416`,
`+9936 -> +10000`, and `+10000 -> +10492`) to `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 lsProg_333 lsmpl
   sepWP_seq_lscl withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (PolynomialError ProtoPolynomialDecoder)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecU8)
open CryptoVerification.SpqrV1.Poly
  (boolByte polyDecoderSize protoPolynomialDecoderAt protoPolynomialDecoderSize
   resultPolyDecoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack loByte)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved decoderFromPbResult decoderFromPbStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbDefsBudget
  (FromPbDecAllocEnv FromPbDecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (decoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

private theorem sub_2400_and_15 (sp : BitVec 64) :
    (sp - 2400#64) &&& 15#64 = sp &&& 15#64 := by
  bv_kernel

alias v6hr_sepWPp_bind_lscl := Variant6ePlaced.v6hr_sepWPp_bind_lscl
alias v6hr_sepWPp_seq_clean_lscl := Variant6ePlaced.v6hr_sepWPp_seq_clean_lscl

/-- `SepWP` sequence helper threading `LibsignalCodeLoaded lsmpl ·.mem` across `mid`. -/
theorem v6hr_sepWP_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q_regs sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWP prog ret sm (P_mid sm) Q) :
    SepWP prog ret s P Q :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpcm hrunm ⟨hPm, hQr⟩ hcl_m =>
    SepWP.weaken_pre hPm (h2 sm hpcm hrunm hcl_m hQr))

/-- `VmPreserved`-strengthened placed `receivingEk = none` branch (`+9936 -> +10416`, Block `333`). -/
theorem v6hr_step_9936_dec_none_to_10416_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (P : SepProp)
    (hl1 : l1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10416#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6ePlaced.v6hr_step_9936_dec_none_to_10416_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out c0 p1_new l1 P hl1
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx24_1) (by simpa using hx25_1)
      (by simpa using hx26_1) (by simpa using hx27_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       by simpa using hx21_m, by simpa using hx26_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v6hr_step_9936_dec_none_to_10416_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (P : SepProp)
    (hl1 : l1.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = noneCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10416#64) s1 (P ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v6hr_step_9936_dec_none_to_10416_placed (ext := ext)
    s0 s1 out c0 p1_new l1 (P ∗ A.pool lim st s1)
    hl1 hpc1 hrun1 hsp1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened placed `receivingEk = some d` setup (`+9936 -> lsmpl.base 376`, Block `333`). -/
theorem v6hr_step_9936_dec_some_to_35448_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          (memRegion ((s0.sp - 2400#64) + 1888#64) polyDecoderSize ∗
           protoPolynomialDecoderAt A ((s0.sp - 2400#64) + 1392#64) d ∗
           A.pool ∗ stackAt (s0.sp - 2400#64) decoderFromPbStack) ∗
          ((((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest)) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        s2.readReg64 .x1 = (s0.sp - 2400#64) + 1392#64 ∧
        s2.readReg64 .x30 = lsmpl.base 333 + 10000#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = p1_new ∧
        s2.readReg64 .x26 = l1 ∧
        s2.readReg64 .x27 = c0 ∧
        TraceCalleeSaved s2 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6ePlaced.v6hr_step_9936_dec_some_to_35448_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out c0 p1_new l1 ptsCap ptsPtr w120 d Rest
      hsp0_align hl1 h1 h2 h3 hw120
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx11_1) (by simpa using hx12_1) (by simpa using hx19_1)
      (by simpa using hx23_1) (by simpa using hx24_1) (by simpa using hx25_1)
      (by simpa using hx26_1) (by simpa using hx27_1) (by simpa using hx28_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun s2 P2 hvm ⟨hP2, hsp2, hx0_2, hx1_2, hx30_2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩ =>
      ⟨hP2, hvm, by simpa using hsp2, by simpa using hx0_2, by simpa using hx1_2,
       by simpa using hx30_2, by simpa using hx19_2, by simpa using hx21_2,
       by simpa using hx26_2, by simpa using hx27_2,
       ⟨by simpa using htr2.1, by simpa using htr2.2⟩⟩

theorem v6hr_step_9936_dec_some_to_35448_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢
          (memRegion ((s0.sp - 2400#64) + 1888#64) polyDecoderSize ∗
           protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) d ∗
           A.pool lim st s2 ∗ stackAt (s0.sp - 2400#64) decoderFromPbStack) ∗
          ((((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
           (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest)) ∧
        VmPreserved s1 s2 ∧
        s2.sp = s0.sp - 2400#64 ∧
        s2.readReg64 .x0 = (s0.sp - 2400#64) + 1888#64 ∧
        s2.readReg64 .x1 = (s0.sp - 2400#64) + 1392#64 ∧
        s2.readReg64 .x30 = lsmpl.base 333 + 10000#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x21 = p1_new ∧
        s2.readReg64 .x26 = l1 ∧
        s2.readReg64 .x27 = c0 ∧
        TraceCalleeSaved s2 s0) := by
  have hwp := v6hr_step_9936_dec_some_to_35448_placed (A := A.repAlloc) (ext := ext)
    s0 s1 out c0 p1_new l1 ptsCap ptsPtr w120 d (A.pool lim st s1 ∗ Rest)
    hsp0_align hl1 h1 h2 h3 hw120 hpc1 hrun1 hsp1
    hx11_1 hx12_1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1
  have hpre_eq :
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest) =
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.repAlloc.pool ∗ (A.pool lim st s1 ∗ Rest)) := by
    simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj]
  rw [hpre_eq]
  refine SepWP.mono hwp fun s2 P2 _ _ ⟨hP2, hvm, hrest⟩ => ?_
  refine ⟨Entails.trans hP2 ?_, hvm, hrest⟩
  rw [← A.pool_of_vmPreserved hvm]
  simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

/-- Total-correctness (`SepWP`) budget-threaded `<PolyDecoder>::from_pb` call step
    (`+9936 -> +10000`, Block `333` calling Block `376`). -/
theorem v6hr_step_9936_dec_some_to_10000_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv d))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10000#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv d evs ∧
          (Pm ⊢
            resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (decoderFromPbResult d) ∗
            memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = p1_new ∧
          sm.readReg64 .x26 = l1 ∧
          sm.readReg64 .x27 = c0 ∧
          TraceCalleeSaved sm s0) := by
  refine v6hr_sepWP_seq_clean_lscl hcl1
    (P_mid := fun s2 =>
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyDecoderSize ∗
       protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) d ∗
       A.pool lim st s2 ∗ stackAt (s0.sp - 2400#64) decoderFromPbStack) ∗
      ((((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
       (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest))
    (v6hr_step_9936_dec_some_to_35448_placed_budget (ext := ext) A lim st s0 s1
      out c0 p1_new l1 ptsCap ptsPtr w120 d Rest
      hsp0_align hl1 h1 h2 h3 hw120 hpc1 hrun1 hsp1
      hx11_1 hx12_1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨_hvm2, hsp2, hx0_2, hx1_2, hx30_2, hx19_2, hx21_2, hx26_2, hx27_2, htr2⟩
  have hsp2_align : s2.spAligned = true := by
    change (s2.sp &&& 15#64 == 0#64) = true
    rw [hsp2, sub_2400_and_15]
    exact hsp0_align
  have hpre_ent :
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyDecoderSize ∗
       protoPolynomialDecoderAt A.repAlloc ((s0.sp - 2400#64) + 1392#64) d ∗
       A.pool lim st s2 ∗ stackAt (s0.sp - 2400#64) decoderFromPbStack) ⊢
      (withLsCodeLoaded lsmpl (decoderFromPbSpec M A lim)).pre
        (⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 1392#64, d⟩, st) s2 := by
    dsimp only [withLsCodeLoaded, decoderFromPbSpec]
    rw [hsp2, sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s2.mem⌝, ← sepConj_assoc]
    exact Entails.pure_right hcl2 (Entails.pure_right ⟨hx0_2, hx1_2, hfits,
      by change LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s2.readReg64 .x30); rw [show s2.readReg64 .x30 = _ from hx30_2]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 333 _ (by decide) (by decide)⟩ (Entails.refl _))
  refine SepWP.call_subroutine_frame hdec
    (x := (⟨(s0.sp - 2400#64) + 1888#64, (s0.sp - 2400#64) + 1392#64, d⟩, st))
    (F := (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
          (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗ Rest)
    hpc2 hrun2 hsp2_align hx30_2
    (fun R' hm => by
      rw [sepConj_assoc] at hm
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm)
    (fun _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    ?_
    (fun _ _ _ hm => False.elim (not_satisfies_false_sepConj hm))
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_f, _, hx21_f, _, _, _, _, hx26_f, hx27_f, _, _, hvregs_f⟩
  dsimp only [withLsCodeLoaded, decoderFromPbSpec]
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_elim; intro evs
  rw [sepConj_assoc]
  apply ProofLib.SepWP.pure_elim; rintro ⟨htr_f, _hacp_f, henv⟩
  apply ProofLib.SepWP.done hpcm hrunm
  refine ⟨evs, henv, ?_, by rw [hspm, hsp2], by rw [hx19_f, hx19_2], by rw [hx21_f, hx21_2],
    by rw [hx26_f, hx26_2], by rw [hx27_f, hx27_2], ⟨htr_f.trans htr2.1, hvregs_f.trans htr2.2⟩⟩
  rw [hsp2]
  dsimp only [protoPolynomialDecoderSize, decoderFromPbStack]
  exact Entails.of_eq (by ac_rfl)

/-- `SepWPp` budget-threaded `<PolyDecoder>::from_pb` call step (`+9936 -> +10000`, Block `333`)
    for any panic postcondition `Qp`. -/
theorem v6hr_step_9936_dec_some_to_10000_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hdec : DefsBudget.DecoderFromPbPlacedOkExt M A lim ext)
    (st : M.σ)
    (s0 s1 : State) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (out c0 p1_new l1 ptsCap ptsPtr w120 : BitVec 64)
    (d : ProtoPolynomialDecoder) (Rest : SepProp)
    (hfits : FitsEnv M lim st (FromPbDecAllocEnv d))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl1 : l1.toNat < 2 ^ 63)
    (h1 : d.pts.length ≤ ptsCap.toNat) (h2 : ptsCap.toNat * 24 < 2 ^ 63) (h3 : ptsPtr ≠ 0#64)
    (hw120 : loByte w120 = boolByte d.isComplete)
    (hpc1 : s1.pc = lsmpl.base 333 + 9936#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx11_1 : s1.readReg64 .x11 = d.ptsNeeded.zeroExtend 64)
    (hx12_1 : s1.readReg64 .x12 = d.polys.zeroExtend 64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 d.pts.length)
    (hx24_1 : s1.readReg64 .x24 = p1_new >>> 8)
    (hx25_1 : s1.readReg64 .x25 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (hx28_1 : s1.readReg64 .x28 = ptsCap)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10000#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
        (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
        memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        (if ptsCap = 0#64 then emp
         else A.repAlloc.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptsPtr d.pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (d.pts.length * 24)) ((ptsCap.toNat - d.pts.length) * 24)) ∗
        A.pool lim st s1 ∗ Rest)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FromPbDecEnv d evs ∧
          (Pm ⊢
            resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (decoderFromPbResult d) ∗
            memRegion ((s0.sp - 2400#64) + 1392#64) 40 ∗
            stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
            (((s0.sp - 2400#64) + 224#64) ↦₆₄ w120) ∗
            (((s0.sp - 2400#64) + 232#64) ↦₆₄ ptsPtr) ∗
            A.pool lim (M.stepEvents evs st) sm ∗ Rest) ∧
          sm.sp = s0.sp - 2400#64 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x21 = p1_new ∧
          sm.readReg64 .x26 = l1 ∧
          sm.readReg64 .x27 = c0 ∧
          TraceCalleeSaved sm s0)
      Qp :=
  SepWPp.of_sepWP_ret
    (v6hr_step_9936_dec_some_to_10000_placed_sepWP hdec st s0 s1 hcl1
      out c0 p1_new l1 ptsCap ptsPtr w120 d Rest hfits
      hsp0_align hl1 h1 h2 h3 hw120 hpc1 hrun1 hsp1
      hx11_1 hx12_1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1)

/-- `VmPreserved`-strengthened placed error-branch step (`+10000 -> +10492`, Block `333`)
    when `<PolyDecoder>::from_pb` returns `.error e`. -/
theorem v6hr_step_10000_err_to_10492_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (e : PolynomialError) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10000#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10492#64) s1
      (resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error e) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Rest) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant6ePlaced.v6hr_step_10000_err_to_10492_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out c0 p1_new l1 e Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx21_1)
      (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, hx21_m, hx26_m, hx27_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx19_m,
       by simpa using hx21_m, by simpa using hx26_m, by simpa using hx27_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v6hr_step_10000_err_to_10492_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out c0 p1_new l1 : BitVec 64) (e : PolynomialError) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10000#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = p1_new)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = c0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10492#64) s1
      (resultPolyDecoderFromPbAt A.repAlloc ((s0.sp - 2400#64) + 1888#64) (.error e) ∗
        Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Rest ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = p1_new ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = c0 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v6hr_step_10000_err_to_10492_placed (A := A.repAlloc) (ext := ext)
    s0 s1 out c0 p1_new l1 e (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx21_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6ePlacedBudget
