/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsfPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsf
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part F

Relocatable Block-`333` `Ok` staging (`+9404 -> +9484 -> +8180 -> ret`) for
`InnerState.headerSent` with `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsfPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder PolyEncoder)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack loByte loBytes7 unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved bv328_toNat epilogueOutFull epilogueStackGaps epilogueStackSlots
   overlapWord7 resultChunkedStatesAt sp_sub_2400_align stackAt_encoderFromPb_split_allocHook
   statesFromPbSavedCells statesFromPbStack v1_encCellsAt v1_midQ128 v1_quadAt v1_w80_b103
   v1_w80_d97 v1_w80_h101 v1_wordAt v1_zext32_setWidth8 v2hsf_bv_add_add_lit
   v2hsf_epilogueOutFull_entails_headerSent v2hsf_epilogueStackGaps_pack
   v2hsf_fsp_1888_entails_epilogue v2hsf_fsp_1936_realign_rest v2hsf_fsp_1936_split_1_7_rest
   v2hsf_fsp_1936_unrealign_rest v2hsf_fsp_1936_unsplit_1_7_rest v2hsf_fsp_576_add_15
   v2hsf_fsp_576_add_15_sext v2hsf_fsp_584_realign_rest v2hsf_fsp_584_unrealign_midQ128_rest
   v2hsf_memRegion_104_72_split v2hsf_memRegion_240_1032_split v2hsf_memRegion_64_32_split
   v2hsf_x25_add_145 v2hsf_x25_add_145_sext)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
  (sessionMemcpyVmAcpSpec subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (FromPbAllocHooksPlacedBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  bv328_toNat
  v2hsf_bv_add_add_lit
  v2hsf_x25_add_145
  v2hsf_x25_add_145_sext
  v2hsf_fsp_576_add_15
  v2hsf_fsp_576_add_15_sext
  v1_w80_d97 v1_w80_h101 v1_w80_b103 v1_zext32_setWidth8

@[local simp]
private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

private theorem align_pre_wp {prog : Program} {target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun s1 P1 => (P1 ⊢ P) ∧ Q s1)) :
    SepWP prog target s P (fun s1 P1 => (P1 ⊢ P_mid) ∧ Q s1) :=
  SepWP.mono hwp fun _ _ _ _ ⟨hp, hq⟩ => ⟨Entails.trans hp h, hq⟩

/-! ## Segment `+9404 -> +9484` (`VmPreserved` & Pool-Threaded) -/

private theorem v2hsf_step_9404_to_9480_placed_raw [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out x20_in ca3 epoch : BitVec 64)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (d92 : BitVec 32) (w104 w112 w120 w192 w592 : BitVec 64) (q576 : BitVec 128) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_in) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9480#64) s
      (((fsp + 92#64) ↦₃₂ d92) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗
        ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
        ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ dw24) ∗ ((fsp + 112#64) ↦₆₄ dw32) ∗ ((fsp + 120#64) ↦₆₄ dw40) ∗
          ((fsp + 192#64) ↦₆₄ dw8) ∗
          ((fsp + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
          ((fsp + 592#64) ↦ₛ loBytes7 (dw64 >>> 8)) ∗
          ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
          ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
          ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
          Rest) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 240#64 ∧ sm.readReg64 .x1 = fsp + 1960#64 ∧
        sm.readReg64 .x2 = 328#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = dw16 ∧
        sm.readReg64 .x21 = fsp + 1392#64 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = x20_in ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = epoch ∧ TraceCalleeSaved sm s0) := by
  subst hsp
  change s.pc = (blkPl_333).base + 9404#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9480#64) s _ _
  wp_simp_pre [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_conv_pre => rw [v2hsf_fsp_1936_realign_rest s.sp dw48 dw56 dw64]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v2hsf_fsp_1936_unrealign_rest s.sp dw48 dw56 dw64,
        v2hsf_fsp_1936_split_1_7_rest s.sp dw48,
        v2hsf_fsp_584_realign_rest s.sp ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) w592]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine align_pre_wp ?_ ?_
  · rw [v2hsf_fsp_584_unrealign_midQ128_rest s.sp dw48 dw56 dw64,
        v2hsf_fsp_1936_unsplit_1_7_rest s.sp dw48]
    simp only [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.of_eq (by sep_ac_rfl)
  · wp_done

private theorem v2hsf_step_9404_to_9480_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out x20_in ca3 epoch : BitVec 64)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (d92 : BitVec 32) (w104 w112 w120 w192 w592 : BitVec 64) (q576 : BitVec 128) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_in) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9480#64) s
      (((fsp + 92#64) ↦₃₂ d92) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗
        ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
        ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ dw24) ∗ ((fsp + 112#64) ↦₆₄ dw32) ∗ ((fsp + 120#64) ↦₆₄ dw40) ∗
          ((fsp + 192#64) ↦₆₄ dw8) ∗
          ((fsp + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
          ((fsp + 592#64) ↦ₛ loBytes7 (dw64 >>> 8)) ∗
          ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
          ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
          ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
          Rest) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 240#64 ∧ sm.readReg64 .x1 = fsp + 1960#64 ∧
        sm.readReg64 .x2 = 328#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = dw16 ∧
        sm.readReg64 .x21 = fsp + 1392#64 ∧ sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = x20_in ∧ sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = epoch ∧ TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (v2hsf_step_9404_to_9480_placed_raw (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out x20_in ca3 epoch dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64
      d92 w104 w112 w120 w192 w592 q576 Rest hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx22) (by simpa using hx23) (by simpa using hx25)
      (by simpa using hx26) (by simpa using hx28)
      ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx2_m, hx19_m, hx20_m, hx21_m,
        hx23_m, hx24_m, hx26_m, hx28_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx2_m, by simpa using hx19_m, by simpa using hx20_m,
       by simpa using hx21_m, by simpa using hx23_m, by simpa using hx24_m,
       by simpa using hx26_m, by simpa using hx28_m,
       ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

/-- `VmPreserved`-strengthened segment `+9404 -> +9484` under `allocMemcpyVmSpec`. -/
theorem v2hsf_step_9404_to_9484_placed_of_memcpy [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_ok :
      subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (fsp out x20_in ca3 epoch : BitVec 64)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328)
    (d92 : BitVec 32) (w104 w112 w120 w192 w592 : BitVec 64) (q576 : BitVec 128) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_in) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9484#64) s
      (stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ d92) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ memRegion (fsp + 240#64) 328 ∗
        ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
        ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
        ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ dw24) ∗ ((fsp + 112#64) ↦₆₄ dw32) ∗ ((fsp + 120#64) ↦₆₄ dw40) ∗
          ((fsp + 192#64) ↦₆₄ dw8) ∗ ((fsp + 240#64) ↦ₛ dbs328) ∗
          ((fsp + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
          ((fsp + 592#64) ↦ₛ loBytes7 (dw64 >>> 8)) ∗
          ((fsp + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) ∗ ((fsp + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) ∗
          ((fsp + 1920#64) ↦₆₄ dw32) ∗ memRegion (fsp + 1928#64) 376 ∗ Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = dw16 ∧
        s1.readReg64 .x21 = fsp + 1392#64 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = x20_in ∧ s1.readReg64 .x26 = ca3 ∧
        s1.readReg64 .x28 = epoch ∧ TraceCalleeSaved s1 s0) := by
  have hpre := v2hsf_step_9404_to_9480_placed (ext := ext) s0 s fsp out x20_in ca3 epoch
    dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 d92 w104 w112 w120 w192 w592 q576
    (stackAt fsp allocHookStack ∗ memRegion (fsp + 240#64) 328 ∗
      ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16 ∗ Rest)
    hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hpre) ?_
  intro sm Pm hpcm hrunm ⟨hPm, hvmm, hspm, hx0m, hx1m, hx2m, hx19m, hx20m, hx21m,
    hx23m, hx24m, hx26m, hx28m, htrm⟩
  refine SepWP.weaken_pre hPm ?_
  have hmemcpy :
      subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpyVmAcpSpec allocHookStack) :=
    subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm allocHookStack hmemcpy_ok
  simp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  subst hspm
  rw [← hdbs328]
  change sm.pc = (blkPl_333).base + 9480#64 at hpcm
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9484#64) sm _ _
  wp_steps 1
  wp_call hmemcpy (sm.sp + 240#64, sm.sp + 1960#64, dbs328)
  have hvm_mc : VmPreserved sm sf := by
    simpa [VmPreserved, LibsignalBinary.Heap.PoolPreserved, LibsignalBinary.Heap.FdsHiFrame,
      wp_norm, arm64_norm] using hpost
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨?_, hvmm.trans hvm_mc, hsp_sf,
    by dsimp only [Reg.x19] at hx19m ⊢; exact Eq.trans ‹_› hx19m,
    by dsimp only [Reg.x20] at hx20m ⊢; exact Eq.trans ‹_› hx20m,
    by dsimp only [Reg.x21] at hx21m ⊢; exact Eq.trans ‹_› hx21m,
    by dsimp only [Reg.x23] at hx23m ⊢; exact Eq.trans ‹_› hx23m,
    by dsimp only [Reg.x24] at hx24m ⊢; exact Eq.trans ‹_› hx24m,
    by dsimp only [Reg.x26] at hx26m ⊢; exact Eq.trans ‹_› hx26m,
    by dsimp only [Reg.x28] at hx28m ⊢; exact Eq.trans ‹_› hx28m,
    ⟨Eq.trans ‹sf.trace = sm.trace› htrm.1, hvregs.trans htrm.2⟩⟩
  have hep1888 := v2hsf_fsp_1888_entails_epilogue sm.sp
    dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 dbs328 hdbs328
  refine Entails.trans (Entails.of_eq (show _ =
    (((sm.sp + 1888#64) ↦₆₄ dw0) ∗ ((sm.sp + 1896#64) ↦₆₄ dw8) ∗ ((sm.sp + 1904#64) ↦₆₄ dw16) ∗
     ((sm.sp + 1912#64) ↦₆₄ dw24) ∗ ((sm.sp + 1920#64) ↦₆₄ dw32) ∗ ((sm.sp + 1928#64) ↦₆₄ dw40) ∗
     ((sm.sp + 1936#64) ↦₆₄ dw48) ∗ ((sm.sp + 1944#64) ↦₆₄ dw56) ∗ ((sm.sp + 1952#64) ↦₆₄ dw64) ∗
     ((sm.sp + 1960#64) ↦ₛ dbs328) ∗ memRegion (sm.sp + 2288#64) 16) ∗
    (stackAt sm.sp 4096 ∗ ((sm.sp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
     ((sm.sp + 104#64) ↦₆₄ dw24) ∗ ((sm.sp + 112#64) ↦₆₄ dw32) ∗ ((sm.sp + 120#64) ↦₆₄ dw40) ∗
     ((sm.sp + 192#64) ↦₆₄ dw8) ∗ ((sm.sp + 240#64) ↦ₛ dbs328) ∗
     ((sm.sp + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
     ((sm.sp + 592#64) ↦ₛ loBytes7 (dw64 >>> 8)) ∗ Rest) by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hep1888) (Entails.of_eq (by sep_ac_rfl))

/-- `VmPreserved`-strengthened segment `+9404 -> +9484` taking `FromPbAllocHooksPlacedBudget`. -/
theorem v2hsf_step_9404_to_9484_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s : State) (fsp out x20_in ca3 epoch : BitVec 64)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328)
    (d92 : BitVec 32) (w104 w112 w120 w192 w592 : BitVec 64) (q576 : BitVec 128) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_in) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9484#64) s
      (stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ d92) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ memRegion (fsp + 240#64) 328 ∗
        ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
        ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
        ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ dw24) ∗ ((fsp + 112#64) ↦₆₄ dw32) ∗ ((fsp + 120#64) ↦₆₄ dw40) ∗
          ((fsp + 192#64) ↦₆₄ dw8) ∗ ((fsp + 240#64) ↦ₛ dbs328) ∗
          ((fsp + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
          ((fsp + 592#64) ↦ₛ loBytes7 (dw64 >>> 8)) ∗
          ((fsp + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) ∗ ((fsp + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) ∗
          ((fsp + 1920#64) ↦₆₄ dw32) ∗ memRegion (fsp + 1928#64) 376 ∗ Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = dw16 ∧
        s1.readReg64 .x21 = fsp + 1392#64 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = x20_in ∧ s1.readReg64 .x26 = ca3 ∧
        s1.readReg64 .x28 = epoch ∧ TraceCalleeSaved s1 s0) :=
  v2hsf_step_9404_to_9484_placed_of_memcpy hA.memcpy_ok s0 s fsp out x20_in ca3 epoch
    dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 dbs328 hdbs328
    d92 w104 w112 w120 w192 w592 q576 Rest
    hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr

theorem v2hsf_step_9404_to_9484_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s : State) (fsp out x20_in ca3 epoch : BitVec 64)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328)
    (d92 : BitVec 32) (w104 w112 w120 w192 w592 : BitVec 64) (q576 : BitVec 128) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_in) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9484#64) s
      (stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ d92) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ memRegion (fsp + 240#64) 328 ∗
        ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ loBytes7 w592) ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
        ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
        ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16 ∗ Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ dw24) ∗ ((fsp + 112#64) ↦₆₄ dw32) ∗ ((fsp + 120#64) ↦₆₄ dw40) ∗
          ((fsp + 192#64) ↦₆₄ dw8) ∗ ((fsp + 240#64) ↦ₛ dbs328) ∗
          ((fsp + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
          ((fsp + 592#64) ↦ₛ loBytes7 (dw64 >>> 8)) ∗
          ((fsp + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) ∗ ((fsp + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) ∗
          ((fsp + 1920#64) ↦₆₄ dw32) ∗ memRegion (fsp + 1928#64) 376 ∗ Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = dw16 ∧
        s1.readReg64 .x21 = fsp + 1392#64 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = x20_in ∧ s1.readReg64 .x26 = ca3 ∧
        s1.readReg64 .x28 = epoch ∧ TraceCalleeSaved s1 s0) := by
  have hwp := v2hsf_step_9404_to_9484_placed hA s0 s fsp out x20_in ca3 epoch
    dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 dbs328 hdbs328
    d92 w104 w112 w120 w192 w592 q576 (Rest ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_transport lim st s s1 hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

/-! ## Copy Block `+9484 -> +8180` (`VmPreserved` & Pool-Threaded) -/

/-- `VmPreserved`-strengthened segment `+9484 -> +8180` (Block `333`). -/
theorem v2hsf_step_9484_to_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch dw0 dw16 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32) (idx : BitVec 32)
    (w160 w208 w224 w832 w864 w880 w888 : BitVec 64) (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9484#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = dw16) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = (loByte (v1_wordAt bs 0)).zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 56#64) ↦₆₄ tag) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
        ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗
        ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ loBytes7 w888) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗ v1_encCellsAt (fsp + 1392#64) bs ∗
        ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 56#64) ↦₆₄ tag) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ ca2) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 208#64) ↦₆₄ v1_wordAt bs 0) ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗
          ((fsp + 224#64) ↦₆₄ epoch) ∗ ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 608#64) ↦₁₂₈ v1_quadAt bs 152) ∗ ((fsp + 624#64) ↦₁₂₈ v1_quadAt bs 168) ∗
          ((fsp + 640#64) ↦₁₂₈ v1_quadAt bs 184) ∗ ((fsp + 656#64) ↦₁₂₈ v1_quadAt bs 200) ∗
          ((fsp + 672#64) ↦₁₂₈ v1_quadAt bs 216) ∗ ((fsp + 688#64) ↦₁₂₈ v1_quadAt bs 232) ∗
          ((fsp + 704#64) ↦₁₂₈ v1_quadAt bs 248) ∗ ((fsp + 720#64) ↦₁₂₈ v1_quadAt bs 264) ∗
          ((fsp + 736#64) ↦₁₂₈ v1_quadAt bs 280) ∗ ((fsp + 752#64) ↦₁₂₈ v1_quadAt bs 296) ∗
          ((fsp + 768#64) ↦₁₂₈ v1_quadAt bs 312) ∗ ((fsp + 784#64) ↦₁₂₈ v1_quadAt bs 328) ∗
          ((fsp + 800#64) ↦₁₂₈ v1_quadAt bs 344) ∗ ((fsp + 816#64) ↦₁₂₈ v1_quadAt bs 360) ∗
          ((fsp + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
          ((fsp + 848#64) ↦₁₂₈ v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) ∗
          ((fsp + 864#64) ↦ₛ loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
          ((fsp + 888#64) ↦ₛ loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗ memRegion (fsp + 1400#64) 392 ∗ Rest) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x6 = fsp + 576#64 ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧ s1.readReg64 .x8 = 4#64 ∧ s1.readReg64 .x15 = tag ∧
        s1.readReg64 .x20 = v1_wordAt bs 8 ∧ s1.readReg64 .x13 = v1_wordAt bs 16 ∧
        s1.readReg64 .x25 = v1_wordAt bs 24 ∧ s1.readReg64 .x30 = v1_wordAt bs 32 ∧
        s1.readReg64 .x9 = v1_wordAt bs 40 ∧ s1.readReg64 .x14 = v1_wordAt bs 48 ∧
        s1.readReg64 .x18 = v1_wordAt bs 56 ∧ s1.readReg64 .x17 = v1_wordAt bs 64 ∧
        s1.readReg64 .x0 = v1_wordAt bs 72 ∧
        s1.readReg32 .x3 = ((v1_wordAt bs 80).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v1_wordAt bs 80).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v1_wordAt bs 80).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v1_wordAt bs 80).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v1_wordAt bs 88 ∧ s1.readReg64 .x5 = v1_wordAt bs 96 ∧
        s1.readReg32 .x21 = (loByte (v1_wordAt bs 104)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v1_wordAt bs 120 ∧ s1.readReg64 .x2 = hi32 ++ idx ∧
        s1.readReg64 .x11 = ca1 ∧ s1.readReg64 .x22 = pa1 ∧ s1.readReg64 .x24 = ca1 ∧
        s1.readReg64 .x10 = pa2 ∧ s1.readReg64 .x26 = ca3 ∧ s1.readReg64 .x12 = pa3 ∧
        s1.readReg64 .x1 = la3 ∧ s1.readReg64 .x28 = dw0 ∧ s1.readReg64 .x16 = dw16 ∧
        TraceCalleeSaved s1 s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsfPlaced.v2hsf_step_9484_to_8180_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch dw0 dw16
      bs hbs hi32 idx w160 w208 w224 w832 w864 w880 w888 d172
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
      Rest hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx20) (by simpa using hx21)
      (by simpa using hx23) (by simpa using hx24) (by simpa using hx26)
      (by simpa using hx28) ⟨by simpa using htr.1, by simpa using htr.2⟩)
    fun s1 P1 hvm ⟨hP1, hsp1, hx6_1, hx19_1, hx23_1, hx8_1, hx15_1, hx20_1, hx13_1,
        hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1, hx3_1, hx27_1, hx27_hi16,
        hx27_hi8, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1, hx10_1,
        hx26_1, hx12_1, hx1_1, hx28_1, hx16_1, htr1⟩ =>
      ⟨hP1, hvm, by simpa using hsp1, by simpa using hx6_1, by simpa using hx19_1,
       by simpa using hx23_1, by simpa using hx8_1, by simpa using hx15_1,
       by simpa using hx20_1, by simpa using hx13_1, by simpa using hx25_1,
       by simpa using hx30_1, by simpa using hx9_1, by simpa using hx14_1,
       by simpa using hx18_1, by simpa using hx17_1, by simpa using hx0_1,
       by simpa using hx3_1, by simpa using hx27_1, by simpa using hx27_hi16,
       by simpa using hx27_hi8, by simpa using hx4_1, by simpa using hx5_1,
       by simpa using hx21_1, by simpa using hx7_1, by simpa using hx2_1,
       by simpa using hx11_1, by simpa using hx22_1, by simpa using hx24_1,
       by simpa using hx10_1, by simpa using hx26_1, by simpa using hx12_1,
       by simpa using hx1_1, by simpa using hx28_1, by simpa using hx16_1,
       ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

theorem v2hsf_step_9484_to_8180_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch dw0 dw16 : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32) (idx : BitVec 32)
    (w160 w208 w224 w832 w864 w880 w888 : BitVec 64) (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Rest : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9484#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = dw16) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = (loByte (v1_wordAt bs 0)).zeroExtend 64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s
      (((fsp + 56#64) ↦₆₄ tag) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
        ((fsp + 172#64) ↦₃₂ d172) ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗
        ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ loBytes7 w888) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗ v1_encCellsAt (fsp + 1392#64) bs ∗
        ((fsp + 1784#64) ↦₆₄ (hi32 ++ idx)) ∗ Rest ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 56#64) ↦₆₄ tag) ∗ ((fsp + 96#64) ↦₆₄ la3) ∗ ((fsp + 160#64) ↦₆₄ ca2) ∗
          ((fsp + 172#64) ↦₃₂ (loByte (v1_wordAt bs 128)).zeroExtend 32) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗ ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 208#64) ↦₆₄ v1_wordAt bs 0) ∗ ((fsp + 216#64) ↦₆₄ dw0) ∗
          ((fsp + 224#64) ↦₆₄ epoch) ∗ ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 608#64) ↦₁₂₈ v1_quadAt bs 152) ∗ ((fsp + 624#64) ↦₁₂₈ v1_quadAt bs 168) ∗
          ((fsp + 640#64) ↦₁₂₈ v1_quadAt bs 184) ∗ ((fsp + 656#64) ↦₁₂₈ v1_quadAt bs 200) ∗
          ((fsp + 672#64) ↦₁₂₈ v1_quadAt bs 216) ∗ ((fsp + 688#64) ↦₁₂₈ v1_quadAt bs 232) ∗
          ((fsp + 704#64) ↦₁₂₈ v1_quadAt bs 248) ∗ ((fsp + 720#64) ↦₁₂₈ v1_quadAt bs 264) ∗
          ((fsp + 736#64) ↦₁₂₈ v1_quadAt bs 280) ∗ ((fsp + 752#64) ↦₁₂₈ v1_quadAt bs 296) ∗
          ((fsp + 768#64) ↦₁₂₈ v1_quadAt bs 312) ∗ ((fsp + 784#64) ↦₁₂₈ v1_quadAt bs 328) ∗
          ((fsp + 800#64) ↦₁₂₈ v1_quadAt bs 344) ∗ ((fsp + 816#64) ↦₁₂₈ v1_quadAt bs 360) ∗
          ((fsp + 832#64) ↦₆₄ v1_wordAt bs 376) ∗
          ((fsp + 848#64) ↦₁₂₈ v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) ∗
          ((fsp + 864#64) ↦ₛ loBytes7 (v1_wordAt bs 144 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) ∗
          ((fsp + 888#64) ↦ₛ loBytes7 (v1_wordAt bs 112 >>> 8)) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗ memRegion (fsp + 1400#64) 392 ∗ Rest ∗ A.pool lim st s1) ∧
        VmPreserved s s1 ∧
        s1.sp = fsp ∧ s1.readReg64 .x6 = fsp + 576#64 ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧ s1.readReg64 .x8 = 4#64 ∧ s1.readReg64 .x15 = tag ∧
        s1.readReg64 .x20 = v1_wordAt bs 8 ∧ s1.readReg64 .x13 = v1_wordAt bs 16 ∧
        s1.readReg64 .x25 = v1_wordAt bs 24 ∧ s1.readReg64 .x30 = v1_wordAt bs 32 ∧
        s1.readReg64 .x9 = v1_wordAt bs 40 ∧ s1.readReg64 .x14 = v1_wordAt bs 48 ∧
        s1.readReg64 .x18 = v1_wordAt bs 56 ∧ s1.readReg64 .x17 = v1_wordAt bs 64 ∧
        s1.readReg64 .x0 = v1_wordAt bs 72 ∧
        s1.readReg32 .x3 = ((v1_wordAt bs 80).extractLsb' 0 8).zeroExtend 32 ∧
        s1.readReg32 .x27 = (v1_wordAt bs 80).extractLsb' 8 32 ∧
        ((s1.readReg64 .x27 >>> 32).setWidth 32).setWidth 16 = (v1_wordAt bs 80).extractLsb' 40 16 ∧
        ((s1.readReg64 .x27 >>> 48).setWidth 32).setWidth 8 = (v1_wordAt bs 80).extractLsb' 56 8 ∧
        s1.readReg64 .x4 = v1_wordAt bs 88 ∧ s1.readReg64 .x5 = v1_wordAt bs 96 ∧
        s1.readReg32 .x21 = (loByte (v1_wordAt bs 104)).zeroExtend 32 ∧
        s1.readReg64 .x7 = v1_wordAt bs 120 ∧ s1.readReg64 .x2 = hi32 ++ idx ∧
        s1.readReg64 .x11 = ca1 ∧ s1.readReg64 .x22 = pa1 ∧ s1.readReg64 .x24 = ca1 ∧
        s1.readReg64 .x10 = pa2 ∧ s1.readReg64 .x26 = ca3 ∧ s1.readReg64 .x12 = pa3 ∧
        s1.readReg64 .x1 = la3 ∧ s1.readReg64 .x28 = dw0 ∧ s1.readReg64 .x16 = dw16 ∧
        TraceCalleeSaved s1 s0) := by
  have hwp := v2hsf_step_9484_to_8180_placed (ext := ext) s0 s fsp out tag ca1 pa1 ca2 pa2
    ca3 pa3 la3 epoch dw0 dw16 bs hbs hi32 idx w160 w208 w224 w832 w864 w880 w888 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
    (Rest ∗ A.pool lim st s) hfsp_align hpc hrun hsp hx19 hx20 hx21 hx23 hx24 hx26 hx28 htr
  refine SepWP.mono hwp fun s1 P1 _ _ ⟨hP1, hvm, hrest⟩ => ?_
  rw [← A.pool_transport lim st s s1 hvm] at hP1
  exact ⟨hP1, hvm, hrest⟩

/-! ## Top-Level `+9404 -> s0.x30` (`v2hsf_headerSent_ok_9404_to_ret_placed`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-threaded composition of `+9404 -> +9484 -> +8180` with
    `states_from_pb_epilogue_8180_placed` and `v2hsf_epilogueOutFull_entails_headerSent`
    under `allocMemcpyVmSpec`. -/
theorem v2hsf_headerSent_ok_9404_to_ret_placed_of_memcpy [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_ok :
      subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32)
    (enc : PolyEncoder) (P_enc_heap : SepProp)
    (henc_reloc : ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
      (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ⊢
        polyEncoderAt A.repAlloc (out + 8#64) enc)
    (dk rootKey macKey : List (BitVec 8)) (hdk : la3 = BitVec.ofNat 64 dk.length)
    (hl1 : ca1 = BitVec.ofNat 64 rootKey.length) (hl2 : ca2 = BitVec.ofNat 64 macKey.length)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328)
    (dec : PolyDecoder) (P_dec_heap : SepProp)
    (hdec_reloc : ((out + 488#64) ↦₆₄ dw0) ∗ (((out + 488#64) + 8#64) ↦₆₄ dw8) ∗
      (((out + 488#64) + 16#64) ↦₆₄ dw16) ∗ (((out + 488#64) + 24#64) ↦₆₄ dw24) ∗
      (((out + 488#64) + 32#64) ↦₆₄ dw32) ∗ (((out + 488#64) + 40#64) ↦₆₄ dw40) ∗
      (((out + 488#64) + 48#64) ↦₆₄ dw48) ∗ (((out + 488#64) + 56#64) ↦₆₄ dw56) ∗
      (((out + 488#64) + 64#64) ↦₆₄ dw64) ∗ (((out + 488#64) + 72#64) ↦ₛ dbs328) ∗
      P_dec_heap ⊢ polyDecoderAt A.repAlloc (out + 488#64) dec)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = (loByte (v1_wordAt bs 0)).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22 : s.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 56 ∗
        ((s0.sp - 2400#64 + 56#64) ↦₆₄ tag) ∗ memRegion (s0.sp - 2400#64 + 64#64) 32 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ la3) ∗ memRegion (s0.sp - 2400#64 + 104#64) 72 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ pa3) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ca1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ dw0) ∗
        memRegion (s0.sp - 2400#64 + 224#64) 8 ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ ca2) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1032 ∗ ((s0.sp - 2400#64 + 1272#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 1280#64) 120 ∗ v1_encCellsAt (s0.sp - 2400#64 + 1392#64) bs ∗
        ((s0.sp - 2400#64 + 1784#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (s0.sp - 2400#64 + 1792#64) 96 ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₆₄ dw0) ∗ ((s0.sp - 2400#64 + 1896#64) ↦₆₄ dw8) ∗
        ((s0.sp - 2400#64 + 1904#64) ↦₆₄ dw16) ∗ ((s0.sp - 2400#64 + 1912#64) ↦₆₄ dw24) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ dw32) ∗ ((s0.sp - 2400#64 + 1928#64) ↦₆₄ dw40) ∗
        ((s0.sp - 2400#64 + 1936#64) ↦₆₄ dw48) ∗ ((s0.sp - 2400#64 + 1944#64) ↦₆₄ dw56) ∗
        ((s0.sp - 2400#64 + 1952#64) ↦₆₄ dw64) ∗ ((s0.sp - 2400#64 + 1960#64) ↦ₛ dbs328) ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
        vecU8Payload A.repAlloc ca3 pa3 dk ∗ vecU8Payload A.repAlloc ca1 pa1 rootKey ∗
        vecU8Payload A.repAlloc ca2 pa2 macKey ∗ Rest ∗ A.pool lim st s)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
          (.ok (.headerSent
            { uc := { auth := { rootKey := rootKey, macKey := macKey }, dk := dk, epoch := epoch },
              sending_ek := enc, receiving_ct1 := dec })) ∗
          Rest ∗ A.pool lim st sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        VmPreserved s sf) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (v2hsf_memRegion_64_32_split (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono (v2hsf_memRegion_104_72_split (s0.sp - 2400#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono
          (Entails.of_eq (ProofLib.memRegion_eight (s0.sp - 2400#64 + 192#64)))
          (sepConj_mono_right (sepConj_mono
            (Entails.of_eq (ProofLib.memRegion_eight (s0.sp - 2400#64 + 208#64)))
            (sepConj_mono_right (sepConj_mono
              (Entails.of_eq (ProofLib.memRegion_eight (s0.sp - 2400#64 + 224#64)))
              (sepConj_mono_right (sepConj_mono_left
                (v2hsf_memRegion_240_1032_split (s0.sp - 2400#64))))))))))))))))) ?_
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
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun w224 =>
    ProofLib.SepWP.exists_left fun w208 => ProofLib.SepWP.exists_left fun w192 =>
    ProofLib.SepWP.exists_left fun d172 => ProofLib.SepWP.exists_left fun w160 =>
    ProofLib.SepWP.exists_left fun w120 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d92 => ?_
  have h9404 := v2hsf_step_9404_to_9484_placed_of_memcpy hmemcpy_ok s0 s (s0.sp - 2400#64) out
    ((loByte (v1_wordAt bs 0)).zeroExtend 64) ca3 epoch
    dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 dbs328 hdbs328 d92 w104 w112 w120 w192 w592 q576
    (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 56 ∗
      ((s0.sp - 2400#64 + 56#64) ↦₆₄ tag) ∗ memRegion (s0.sp - 2400#64 + 64#64) 28 ∗
      ((s0.sp - 2400#64 + 96#64) ↦₆₄ la3) ∗ memRegion (s0.sp - 2400#64 + 128#64) 32 ∗
      ((s0.sp - 2400#64 + 160#64) ↦₆₄ w160) ∗ memRegion (s0.sp - 2400#64 + 168#64) 4 ∗
      ((s0.sp - 2400#64 + 172#64) ↦₃₂ d172) ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ pa3) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ca1) ∗
      ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ dw0) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ ca2) ∗
      memRegion (s0.sp - 2400#64 + 568#64) 8 ∗ memRegion (s0.sp - 2400#64 + 599#64) 9 ∗
      ((s0.sp - 2400#64 + 608#64) ↦₁₂₈ q608) ∗ ((s0.sp - 2400#64 + 624#64) ↦₁₂₈ q624) ∗
      ((s0.sp - 2400#64 + 640#64) ↦₁₂₈ q640) ∗ ((s0.sp - 2400#64 + 656#64) ↦₁₂₈ q656) ∗
      ((s0.sp - 2400#64 + 672#64) ↦₁₂₈ q672) ∗ ((s0.sp - 2400#64 + 688#64) ↦₁₂₈ q688) ∗
      ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
      ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
      ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
      ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
      ((s0.sp - 2400#64 + 832#64) ↦₆₄ w832) ∗ memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
      ((s0.sp - 2400#64 + 848#64) ↦₁₂₈ q848) ∗ ((s0.sp - 2400#64 + 864#64) ↦ₛ loBytes7 w864) ∗
      memRegion (s0.sp - 2400#64 + 871#64) 9 ∗ ((s0.sp - 2400#64 + 880#64) ↦₆₄ w880) ∗
      ((s0.sp - 2400#64 + 888#64) ↦ₛ loBytes7 w888) ∗
      memRegion (s0.sp - 2400#64 + 895#64) 377 ∗ ((s0.sp - 2400#64 + 1272#64) ↦₆₄ pa1) ∗
      memRegion (s0.sp - 2400#64 + 1280#64) 120 ∗ v1_encCellsAt (s0.sp - 2400#64 + 1392#64) bs ∗
      ((s0.sp - 2400#64 + 1784#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (s0.sp - 2400#64 + 1792#64) 96 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
      vecU8Payload A.repAlloc ca3 pa3 dk ∗ vecU8Payload A.repAlloc ca1 pa1 rootKey ∗
      vecU8Payload A.repAlloc ca2 pa2 macKey ∗ Rest ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) h9404) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hvm1, hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx26_1, hx28_1, htr1⟩
  rw [← A.pool_transport lim st s s1 hvm1] at hP1
  have h9484 := v2hsf_step_9484_to_8180_placed (ext := ext) s0 s1 (s0.sp - 2400#64) out tag
    ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch dw0 dw16 bs hbs hi32 enc.idx
    w160 w208 w224 w832 w864 w880 w888 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ ((s0.sp - 2400#64 + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
      ((s0.sp - 2400#64 + 104#64) ↦₆₄ dw24) ∗ ((s0.sp - 2400#64 + 112#64) ↦₆₄ dw32) ∗
      ((s0.sp - 2400#64 + 120#64) ↦₆₄ dw40) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ dw8) ∗
      ((s0.sp - 2400#64 + 240#64) ↦ₛ dbs328) ∗ ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
      ((s0.sp - 2400#64 + 592#64) ↦ₛ loBytes7 (dw64 >>> 8)) ∗
      ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) ∗
      ((s0.sp - 2400#64 + 1920#64) ↦₆₄ dw32) ∗ memRegion (s0.sp - 2400#64 + 1928#64) 376 ∗
      memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 56 ∗
      memRegion (s0.sp - 2400#64 + 64#64) 28 ∗ memRegion (s0.sp - 2400#64 + 128#64) 32 ∗
      memRegion (s0.sp - 2400#64 + 168#64) 4 ∗ memRegion (s0.sp - 2400#64 + 568#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 599#64) 9 ∗ memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 871#64) 9 ∗ memRegion (s0.sp - 2400#64 + 895#64) 377 ∗
      memRegion (s0.sp - 2400#64 + 1280#64) 120 ∗ memRegion (s0.sp - 2400#64 + 1792#64) 96 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
      vecU8Payload A.repAlloc ca3 pa3 dk ∗ vecU8Payload A.repAlloc ca1 pa1 rootKey ∗
      vecU8Payload A.repAlloc ca2 pa2 macKey ∗ Rest ∗ A.pool lim st s1)
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx26_1 hx28_1 htr1
  refine SepWP.seq (SepWP.weaken_pre (Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))) h9484) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hvm2, hsp2, hx6_2, hx19_2, hx23_2, hx8_2, hx15_2, hx20_2, hx13_2,
    hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_2, hx27_hi16, hx27_hi8,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2,
    hx1_2, hx28_2, hx16_2, htr2⟩
  rw [← A.pool_transport lim st s1 s2 hvm2] at hP2
  have hgaps := v2hsf_epilogueStackGaps_pack (s0.sp - 2400#64) tag la3 pa3 pa2 ca1 dw0 pa1
  have hP2' : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64) ((loByte dw48).zeroExtend 32)
        ((loByte (v1_wordAt bs 128)).zeroExtend 32) dw24 dw32 dw40 ca2 dw8 (v1_wordAt bs 0) epoch ca2 dbs328
        (v1_midQ128 dw48 dw56 dw64) (dw64 >>> 8)
        (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
        (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
        (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
        (v1_quadAt bs 344) (v1_quadAt bs 360) (v1_wordAt bs 376)
        (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) (v1_wordAt bs 144 >>> 8)
        (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) (v1_wordAt bs 112 >>> 8)
        (dw8 ++ dw0) (dw24 ++ dw16) dw32 ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (P_enc_heap ∗ P_dec_heap ∗
       vecU8Payload A.repAlloc ca3 pa3 dk ∗ vecU8Payload A.repAlloc ca1 pa1 rootKey ∗
       vecU8Payload A.repAlloc ca2 pa2 macKey ∗ Rest) ∗
      A.pool lim st s2 := by
    refine Entails.trans hP2 ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]; unfold epilogueStackSlots
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hgaps))))
    exact Entails.of_eq (by sep_ac_rfl)
  have hep :=
    LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux.states_from_pb_epilogue_8180_placed
      A lim st hmemcpy_ok s0 s2 out
    ((loByte dw48).zeroExtend 32) ((loByte (v1_wordAt bs 128)).zeroExtend 32)
    dw24 dw32 dw40 ca2 dw8 (v1_wordAt bs 0) epoch ca2 dbs328 hdbs328
    (v1_midQ128 dw48 dw56 dw64) (dw64 >>> 8)
    (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
    (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
    (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
    (v1_quadAt bs 344) (v1_quadAt bs 360) (v1_wordAt bs 376)
    (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) (v1_wordAt bs 144 >>> 8)
    (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) (v1_wordAt bs 112 >>> 8)
    (dw8 ++ dw0) (dw24 ++ dw16) dw32
    (P_enc_heap ∗ P_dec_heap ∗
     vecU8Payload A.repAlloc ca3 pa3 dk ∗ vecU8Payload A.repAlloc ca1 pa1 rootKey ∗
     vecU8Payload A.repAlloc ca2 pa2 macKey ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  refine SepWP.weaken_pre hP2' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f, hvm3⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f, (hvm1.trans hvm2).trans hvm3⟩
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2,
      hx3_2, v1_zext32_setWidth8, hx27_2, hx27_hi16, hx27_hi8, hx4_2, hx5_2,
      hx21_2, v1_zext32_setWidth8, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2,
      hx26_2, hx12_2, hx1_2, hx28_2, hx16_2]
  have hout := v2hsf_epilogueOutFull_entails_headerSent A.repAlloc (F := F)
    out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch bs hbs hi32 enc P_enc_heap henc_reloc
    dk rootKey macKey hdk hl1 hl2 dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64
    dbs328 hdbs328 dec P_dec_heap hdec_reloc (dw8 ++ dw0) (dw24 ++ dw16) dw32
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (Entails.trans (sepConj_mono_left hout)
    (Entails.of_eq (by sep_ac_rfl)))

/-- Budget-threaded top-level `+9404 -> s0.x30` theorem for Variant 2 (`HeaderSent`, Block `333`)
    under `FromPbAllocHooksPlacedBudget`. -/
theorem v2hsf_headerSent_ok_9404_to_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext) (st : M.σ)
    (s0 s : State) (out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32)
    (enc : PolyEncoder) (P_enc_heap : SepProp)
    (henc_reloc : ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
      (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ⊢
        polyEncoderAt A.repAlloc (out + 8#64) enc)
    (dk rootKey macKey : List (BitVec 8)) (hdk : la3 = BitVec.ofNat 64 dk.length)
    (hl1 : ca1 = BitVec.ofNat 64 rootKey.length) (hl2 : ca2 = BitVec.ofNat 64 macKey.length)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328)
    (dec : PolyDecoder) (P_dec_heap : SepProp)
    (hdec_reloc : ((out + 488#64) ↦₆₄ dw0) ∗ (((out + 488#64) + 8#64) ↦₆₄ dw8) ∗
      (((out + 488#64) + 16#64) ↦₆₄ dw16) ∗ (((out + 488#64) + 24#64) ↦₆₄ dw24) ∗
      (((out + 488#64) + 32#64) ↦₆₄ dw32) ∗ (((out + 488#64) + 40#64) ↦₆₄ dw40) ∗
      (((out + 488#64) + 48#64) ↦₆₄ dw48) ∗ (((out + 488#64) + 56#64) ↦₆₄ dw56) ∗
      (((out + 488#64) + 64#64) ↦₆₄ dw64) ∗ (((out + 488#64) + 72#64) ↦ₛ dbs328) ∗
      P_dec_heap ⊢ polyDecoderAt A.repAlloc (out + 488#64) dec)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = (loByte (v1_wordAt bs 0)).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22 : s.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = epoch)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 56 ∗
        ((s0.sp - 2400#64 + 56#64) ↦₆₄ tag) ∗ memRegion (s0.sp - 2400#64 + 64#64) 32 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ la3) ∗ memRegion (s0.sp - 2400#64 + 104#64) 72 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ pa3) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ca1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ dw0) ∗
        memRegion (s0.sp - 2400#64 + 224#64) 8 ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ ca2) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1032 ∗ ((s0.sp - 2400#64 + 1272#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 1280#64) 120 ∗ v1_encCellsAt (s0.sp - 2400#64 + 1392#64) bs ∗
        ((s0.sp - 2400#64 + 1784#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (s0.sp - 2400#64 + 1792#64) 96 ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₆₄ dw0) ∗ ((s0.sp - 2400#64 + 1896#64) ↦₆₄ dw8) ∗
        ((s0.sp - 2400#64 + 1904#64) ↦₆₄ dw16) ∗ ((s0.sp - 2400#64 + 1912#64) ↦₆₄ dw24) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ dw32) ∗ ((s0.sp - 2400#64 + 1928#64) ↦₆₄ dw40) ∗
        ((s0.sp - 2400#64 + 1936#64) ↦₆₄ dw48) ∗ ((s0.sp - 2400#64 + 1944#64) ↦₆₄ dw56) ∗
        ((s0.sp - 2400#64 + 1952#64) ↦₆₄ dw64) ∗ ((s0.sp - 2400#64 + 1960#64) ↦ₛ dbs328) ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
        vecU8Payload A.repAlloc ca3 pa3 dk ∗ vecU8Payload A.repAlloc ca1 pa1 rootKey ∗
        vecU8Payload A.repAlloc ca2 pa2 macKey ∗ Rest ∗ A.pool lim st s)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A.repAlloc (F := F) out
          (.ok (.headerSent
            { uc := { auth := { rootKey := rootKey, macKey := macKey }, dk := dk, epoch := epoch },
              sending_ek := enc, receiving_ct1 := dec })) ∗
          Rest ∗ A.pool lim st sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        VmPreserved s sf) :=
  v2hsf_headerSent_ok_9404_to_ret_placed_of_memcpy A lim st hA.memcpy_ok s0 s out tag
    ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch bs hbs hi32 enc P_enc_heap henc_reloc
    dk rootKey macKey hdk hl1 hl2 dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64
    dbs328 hdbs328 dec P_dec_heap hdec_reloc Rest hsp0_align hpc hrun hsp
    hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsfPlacedBudget
