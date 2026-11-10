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
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Dispatch, Epilogue, and `KeysUnsampled` Leaves

Jump-table dispatch (`+36`), shared `Ok` epilogues (`+8176` / `+8180`), and `KeysUnsampled`
early-error and unpack leaves in Block `333` with `VmPreserved` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap
open CryptoVerification (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize none2Cap optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.ProtoRepr (AuthenticatorPBGhost authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.States.FromPb (TaggedVariantDispatch TraceCalleeSaved epilogueOutFull epilogueOutFull_entails_64_864 epilogueOutPartA epilogueOutPartANo145 epilogueOutPartA_eq_no145 epilogueOutPartBPost epilogueOutPartBPre epilogueStackGaps epilogueStackPartA epilogueStackPartA_realign_eq epilogueStackPartBPost epilogueStackPartBPre epilogueStackPost_entails_2304 epilogueStackSlots memRegion_2088_entails_epilogue_hi memRegion_208_entails_epilogue_lo memRegion_out_928_split_8 memRegion_out_partA_split memRegion_out_partB_split memRegion_out_partC_split overlapWord7 resultChunkedStatesAt sp_sub_2400_align stackAt_encoderFromPb_split_allocHook statesFromPbJumpTablePlacedAt statesFromPbSavedCells statesFromPbStack)
open CryptoVerification.SpqrV1.Unchunked (extractLsb'_0_64_append extractLsb'_64_64_append vecU8Payload)

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[local simp]
private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

/-! ## `VmPreserved` & Budget-Threaded Jump-Table Dispatch (`+36 -> +off` / `+1056`) -/

/-- Relocatable jump-table dispatch (`+36 -> +off` in Block `333`) with `VmPreserved`. -/
theorem states_from_pb_dispatch_tagged_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA tag off : BitVec 64) (Rest : SepProp)
    (htag : TaggedVariantDispatch tag off)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + off) s1
      ((pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0 ∧
        VmPreserved s1 sm) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.states_from_pb_dispatch_tagged_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA tag off Rest htag
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx8_1) (by simpa using hx0_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19, hx27, hx0, hx25, hx21, hx13, hx23, htr_m⟩ =>
      ⟨hPm, hsp_m, hx19, hx27, hx0, hx25, hx21, hx13, hx23, htr_m, hvm⟩

theorem states_from_pb_dispatch_tagged_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA tag off : BitVec 64) (Rest : SepProp)
    (htag : TaggedVariantDispatch tag off)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + off) s1
      ((pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗ Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ tag) ∗ statesFromPbJumpTablePlacedAt ∗ Rest ∗ A.pool lim st sm) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0 ∧
        VmPreserved s1 sm) := by
  have h := states_from_pb_dispatch_tagged_placed (ext := ext) s0 s1 out pbA tag off
    (Rest ∗ A.pool lim st s1) htag hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono h ?_)
  intro sm Pm _ _ ⟨hPm, hrest⟩
  have hvm : VmPreserved s1 sm := hrest.2.2.2.2.2.2.2.2.2
  refine ⟨Entails.trans hPm ?_, hrest⟩
  rw [A.pool_transport lim st s1 sm hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Relocatable jump-table dispatch (`+36 -> +1056` in Block `333`) for `Ct1Sampled` with
    `VmPreserved`. -/
theorem states_from_pb_dispatch_ct1Sampled_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA w0 : BitVec 64) (Rest : SepProp)
    (hw0 : w0 = noneCap ∨ w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1056#64) s1
      ((pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0 ∧
        VmPreserved s1 sm) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.states_from_pb_dispatch_ct1Sampled_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA w0 Rest hw0
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx8_1) (by simpa using hx0_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19, hx27, hx0, hx25, hx21, hx13, hx23, htr_m⟩ =>
      ⟨hPm, hsp_m, hx19, hx27, hx0, hx25, hx21, hx13, hx23, htr_m, hvm⟩

theorem states_from_pb_dispatch_ct1Sampled_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA w0 : BitVec 64) (Rest : SepProp)
    (hw0 : w0 = noneCap ∨ w0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = out)
    (hx0_1 : s1.readReg64 .x0 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1056#64) s1
      ((pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ (pbA ↦₆₄ w0) ∗ statesFromPbJumpTablePlacedAt ∗ Rest ∗ A.pool lim st sm) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x0 = pbA ∧
        sm.readReg64 .x25 = s0.sp - 608#64 ∧
        sm.readReg64 .x21 = s0.sp - 1008#64 ∧
        sm.readReg64 .x13 = s0.sp - 1136#64 ∧
        sm.readReg64 .x23 = s0.sp - 1552#64 ∧
        TraceCalleeSaved sm s0 ∧
        VmPreserved s1 sm) := by
  have h := states_from_pb_dispatch_ct1Sampled_placed (ext := ext) s0 s1 out pbA w0
    (Rest ∗ A.pool lim st s1) hw0 hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono h ?_)
  intro sm Pm _ _ ⟨hPm, hrest⟩
  have hvm : VmPreserved s1 sm := hrest.2.2.2.2.2.2.2.2.2
  refine ⟨Entails.trans hPm ?_, hrest⟩
  rw [A.pool_transport lim st s1 sm hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## `VmPreserved` & Budget-Threaded Shared `Ok` Epilogue Wrapper (`+8180 / +8176 -> s0.x30`) -/

theorem epilogue_step_8180_8284_region_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (w208 w880 : BitVec 64)
    (q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8284#64)
      s
      ((memRegion out 103 ∗ memRegion (out + 145#64) 16 ∗ memRegion (out + 264#64) 128) ∗
       epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutPartANo145 out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            q704 q720 q736 q752 q768 q784 q800 q816 ∗
          ((out + 145#64) ↦₁₂₈ q848) ∗
          epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
          Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 560#64 ∧
        sm.readReg64 .x1 = s.readReg64 .x1 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x4 = s.readReg64 .x4 ∧
        sm.readReg64 .x5 = s.readReg64 .x5 ∧
        sm.readReg64 .x6 = s.readReg64 .x6 ∧
        sm.readReg64 .x7 = s.readReg64 .x7 ∧
        sm.readReg32 .x8 = (s.readReg64 .x27 >>> 48).setWidth 32 ∧
        sm.readReg64 .x9 = w880 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧
        sm.readReg64 .x11 = s.readReg64 .x11 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧
        sm.readReg64 .x16 = s.readReg64 .x16 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg32 .x21 = s.readReg32 .x21 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_partA_split out)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro uq376; apply ProofLib.SepWP.exists_left; intro uq360
  apply ProofLib.SepWP.exists_left; intro uq344; apply ProofLib.SepWP.exists_left; intro uq328
  apply ProofLib.SepWP.exists_left; intro uq312; apply ProofLib.SepWP.exists_left; intro uq296
  apply ProofLib.SepWP.exists_left; intro uq280; apply ProofLib.SepWP.exists_left; intro uq264
  apply ProofLib.SepWP.exists_left; intro uq145; apply ProofLib.SepWP.exists_left; intro uh101
  apply ProofLib.SepWP.exists_left; intro ud97; apply ProofLib.SepWP.exists_left; intro ub96
  apply ProofLib.SepWP.exists_left; intro u88; apply ProofLib.SepWP.exists_left; intro u80
  apply ProofLib.SepWP.exists_left; intro u72; apply ProofLib.SepWP.exists_left; intro u64
  apply ProofLib.SepWP.exists_left; intro u56; apply ProofLib.SepWP.exists_left; intro u48
  apply ProofLib.SepWP.exists_left; intro u40; apply ProofLib.SepWP.exists_left; intro u32
  apply ProofLib.SepWP.exists_left; intro u24; apply ProofLib.SepWP.exists_left; intro u16
  apply ProofLib.SepWP.exists_left; intro u8; apply ProofLib.SepWP.exists_left; intro u0
  have hstep := EpiloguePlacedBudget.epilogue_step_8180_8284_placed (ext := ext) s fsp out
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88
    ub96 ud97 uh101 uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376
    w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 Frame
    hfsp_align hpc hrun hsp hx19
  refine SepWP.weaken_pre ?_ (SepWP.mono hstep ?_)
  · unfold epilogueOutPartA
    exact Entails.of_eq (by sep_ac_rfl)
  · intro sm Pm _ _ ⟨hPm, hregs⟩
    refine ⟨Entails.trans hPm ?_, hregs⟩
    rw [epilogueOutPartA_eq_no145]
    exact Entails.of_eq (by sep_ac_rfl)

theorem epilogue_step_8284_8468_region_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64) (q848 : BitVec 128) (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887 : BitVec 64)
    (q576 q608 q624 q640 q656 q672 q688 : BitVec 128) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64) (hx6 : s.readReg64 .x6 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = fsp + 848#64) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8468#64) s
      ((memRegion (out + 103#64) 42 ∗ (((out + 145#64) ↦₁₂₈ q848) ∗ memRegion (out + 161#64) 7) ∗
        memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168) ∗
       epilogueStackPartBPre fsp d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
         q576 q608 q624 q640 q656 q672 q688 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
          ((out + 153#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
          epilogueOutPartBPost out
            ((s.readReg32 .x8).setWidth 8) (s.readReg64 .x4) (s.readReg64 .x5)
            ((s.readReg32 .x21).setWidth 8) (s.readReg64 .x9) w887 (s.readReg64 .x7)
            (d172.setWidth 8) w863 q608 q624 q640 q656 q672 q688
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) ∗
          epilogueStackPartBPost fsp d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
            q576 q608 q624 q640 q656 q672 q688 ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = out + 560#64 ∧ sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x2 = 328#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_partB_split out q848)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u552; apply ProofLib.SepWP.exists_left; intro u545
  apply ProofLib.SepWP.exists_left; intro u537; apply ProofLib.SepWP.exists_left; intro ub536
  apply ProofLib.SepWP.exists_left; intro u528; apply ProofLib.SepWP.exists_left; intro u520
  apply ProofLib.SepWP.exists_left; intro u512; apply ProofLib.SepWP.exists_left; intro u504
  apply ProofLib.SepWP.exists_left; intro u496; apply ProofLib.SepWP.exists_left; intro u488
  apply ProofLib.SepWP.exists_left; intro u480; apply ProofLib.SepWP.exists_left; intro u472
  apply ProofLib.SepWP.exists_left; intro u464; apply ProofLib.SepWP.exists_left; intro u456
  apply ProofLib.SepWP.exists_left; intro u448; apply ProofLib.SepWP.exists_left; intro u440
  apply ProofLib.SepWP.exists_left; intro u432; apply ProofLib.SepWP.exists_left; intro u424
  apply ProofLib.SepWP.exists_left; intro u416; apply ProofLib.SepWP.exists_left; intro u408
  apply ProofLib.SepWP.exists_left; intro u400; apply ProofLib.SepWP.exists_left; intro u392
  apply ProofLib.SepWP.exists_left; intro uq248; apply ProofLib.SepWP.exists_left; intro uq232
  apply ProofLib.SepWP.exists_left; intro uq216; apply ProofLib.SepWP.exists_left; intro uq200
  apply ProofLib.SepWP.exists_left; intro uq184; apply ProofLib.SepWP.exists_left; intro uq168
  apply ProofLib.SepWP.exists_left; intro u160; apply ProofLib.SepWP.exists_left; intro ub144
  apply ProofLib.SepWP.exists_left; intro u136; apply ProofLib.SepWP.exists_left; intro u128
  apply ProofLib.SepWP.exists_left; intro u121; apply ProofLib.SepWP.exists_left; intro ub120
  apply ProofLib.SepWP.exists_left; intro u112; apply ProofLib.SepWP.exists_left; intro u104
  apply ProofLib.SepWP.exists_left; intro ub103
  have hstep := EpiloguePlacedBudget.epilogue_step_8284_8468_placed (ext := ext) s fsp out
    ub103 u104 u112 ub120 u121 u128 u136 ub144 u160 uq168 uq184 uq200 uq216 uq232 uq248
    u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528
    ub536 u537 u545 u552 d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
    q576 q608 q624 q640 q656 q672 q688
    (((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
     ((out + 153#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗ Frame)
    hfsp_align hpc hrun hsp hx0 hx6 hx19 hx23
  refine SepWP.weaken_pre ?_ (SepWP.mono hstep ?_)
  · unfold epilogueOutPartBPre; exact Entails.of_eq (by sep_ac_rfl)
  · intro sm Pm _ _ ⟨hPm, hregs⟩; exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hregs⟩

theorem epilogue_step_8468_64_region_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64) (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64) (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64) s
      (stackAt fsp allocHookStack ∗ memRegion (out + 560#64) 368 ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          (((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q1888) ∗
           ((out + 904#64) ↦₁₂₈ q1904) ∗ ((out + 920#64) ↦₆₄ w1920)) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗ ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_partC_split out))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u920
  apply ProofLib.SepWP.exists_left; intro uq904
  apply ProofLib.SepWP.exists_left; intro uq888
  have hstep := EpiloguePlacedBudget.epilogue_step_8468_64_placed hmemcpy_ok s fsp out bs240 hbs240
    uq888 uq904 q1888 q1904 u920 w1920 Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep ?_)
  intro sm Pm _ _ ⟨hPm, hregs⟩
  exact ⟨Entails.trans hPm (Entails.of_eq (by sep_ac_rfl)), hregs⟩

/-- Relocatable complete shared `Ok` epilogue from `+8180` to `s0.x30` in Block `333`. -/

theorem states_from_pb_epilogue_8180_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8180#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx6 : s.readReg64 .x6 = (s0.sp - 2400#64) + 576#64) (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame ∗
       A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame ∗ A.pool lim st sm) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace ∧
        VmPreserved s sm) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp halign
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (memRegion_out_928_split_8 out))) ?_
  unfold epilogueStackSlots
  refine SepWP.seq (epilogue_step_8180_8284_region_placed (ext := ext) s (s0.sp - 2400#64) out w208 w880
    q704 q720 q736 q752 q768 q784 q800 q816 q848
    (((s0.sp - 2400#64 + 864#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 w864) ∗
     ((s0.sp - 2400#64 + 888#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 w888) ∗
     memRegion (out + 103#64) 42 ∗ memRegion (out + 161#64) 7 ∗
     memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168 ∗ memRegion (out + 560#64) 368 ∗
     ((s0.sp - 2400#64 + 92#64) ↦₃₂ d92) ∗
     ((s0.sp - 2400#64 + 104#64) ↦₆₄ w104) ∗ ((s0.sp - 2400#64 + 112#64) ↦₆₄ w112) ∗
     ((s0.sp - 2400#64 + 120#64) ↦₆₄ w120) ∗ ((s0.sp - 2400#64 + 160#64) ↦₆₄ w160) ∗
     ((s0.sp - 2400#64 + 172#64) ↦₃₂ d172) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ w192) ∗
     ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
     ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240) ∗
     ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ q576) ∗ ((s0.sp - 2400#64 + 592#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 w592) ∗
     ((s0.sp - 2400#64 + 608#64) ↦₁₂₈ q608) ∗ ((s0.sp - 2400#64 + 624#64) ↦₁₂₈ q624) ∗
     ((s0.sp - 2400#64 + 640#64) ↦₁₂₈ q640) ∗ ((s0.sp - 2400#64 + 656#64) ↦₁₂₈ q656) ∗
     ((s0.sp - 2400#64 + 672#64) ↦₁₂₈ q672) ∗ ((s0.sp - 2400#64 + 688#64) ↦₁₂₈ q688) ∗
     ((s0.sp - 2400#64 + 832#64) ↦₆₄ w832) ∗
     ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ q1888) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ q1904) ∗
     ((s0.sp - 2400#64 + 1920#64) ↦₆₄ w1920) ∗
     memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ stackAt (s0.sp - 2400#64) allocHookStack ∗
     epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ (Frame ∗ A.pool lim st s))
    hfsp_align hpc hrun hsp hx19 |>
    SepWP.weaken_pre (by unfold epilogueStackPartA; exact Entails.of_eq (by sep_ac_rfl))) ?_
  intro sA PA hpcA hrunA ⟨hPA, hvmA, hspA, hx0A, hx1A, hx2A, hx4A, hx5A, hx6A, hx7A, hx8A, hx9A,
    hx10A, hx11A, hx12A, hx16A, hx19A, hx21A, hx22A, hx23A, hx24A, hx26A, hx28A, _, htrA⟩
  have hPA' : PA ⊢
      ((memRegion (out + 103#64) 42 ∗ (((out + 145#64) ↦₁₂₈ q848) ∗ memRegion (out + 161#64) 7) ∗
        memRegion (out + 168#64) 96 ∗ memRegion (out + 392#64) 168) ∗
       epilogueStackPartBPre (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 w224 w232 w592
         w832 (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
         q576 q608 q624 q640 q656 q672 q688 ∗
       (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
        memRegion (out + 560#64) 368 ∗ ((s0.sp - 2400#64 + 240#64) ↦ₛ bs240) ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ q1888) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ q1904) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ w1920) ∗
        epilogueOutPartANo145 out
          (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
          (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
          (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
          ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
          (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
          q704 q720 q736 q752 q768 q784 q800 q816 ∗
        ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
        ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
        ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
        ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
        ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
        ((s0.sp - 2400#64 + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
        ((s0.sp - 2400#64 + 856#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
        ((s0.sp - 2400#64 + 880#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 w880) ∗
        epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ (Frame ∗ A.pool lim st s))) := by
    refine Entails.trans hPA ?_
    rw [sepConj_assoc, sepConj_assoc, ← sepConj_assoc (epilogueStackPartA _ _ _ _ _ _ _ _ _ _ _ _),
        ← sepConj_assoc (epilogueStackPartA _ _ _ _ _ _ _ _ _ _ _ _ ∗ _),
        epilogueStackPartA_realign_eq]
    unfold epilogueStackPartBPre
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.seq (SepWP.weaken_pre hPA' (epilogue_step_8284_8468_region_placed (ext := ext) sA (s0.sp - 2400#64) out q848
    d92 d172 w104 w112 w120 w160 w192 w224 w232 w592 w832
    (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
    q576 q608 q624 q640 q656 q672 q688 _
    hfsp_align hpcA hrunA hspA hx0A (hx6A.trans hx6) hx19A (hx23A.trans hx23))) ?_
  intro sB PB hpcB hrunB ⟨hPB, hvmB, hspB, hx0B, hx1B, hx2B, hx19B, _, htrB⟩
  rw [hx8A, hx4A, hx5A, hx21A, hx9A, hx7A, hx2A, hx11A, hx22A, hx24A, hx10A, hx26A, hx12A, hx1A, hx28A, hx16A] at hPB
  refine SepWP.seq (SepWP.weaken_pre (Entails.trans hPB (Entails.of_eq (by sep_ac_rfl)))
    (epilogue_step_8468_64_region_placed hmemcpy_ok sB (s0.sp - 2400#64) out bs240 hbs240 q1888 q1904 w1920
      (((out + 145#64) ↦₆₄ q848.extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
       epilogueOutPartBPost out
         (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
         (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
         w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
         (d172.setWidth 8) (overlapWord7 (q848.extractLsb' 64 64) w864)
         q608 q624 q640 q656 q672 q688
         w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
         (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
         (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
         (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
         w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) ∗
       epilogueStackPartBPost (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 w224 w232 w592
         w832 (overlapWord7 (q848.extractLsb' 64 64) w864) (overlapWord7 w880 w888)
         q576 q608 q624 q640 q656 q672 q688 ∗
       memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       epilogueOutPartANo145 out
         (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
         (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
         (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
         ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
         (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
         q704 q720 q736 q752 q768 q784 q800 q816 ∗
       ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗
       ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
       ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
       ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
       ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
       ((s0.sp - 2400#64 + 848#64) ↦₆₄ q848.extractLsb' 0 64) ∗
       ((s0.sp - 2400#64 + 856#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (q848.extractLsb' 64 64)) ∗
       ((s0.sp - 2400#64 + 880#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 w880) ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ (Frame ∗ A.pool lim st s))
      hfsp_align hpcB hrunB hspB hx0B hx1B hx2B hx19B)) ?_
  intro sC PC hpcC hrunC ⟨hPC, hvmC, hspC, htrC⟩
  have hvm_sC : VmPreserved s sC := hvmA.trans (hvmB.trans hvmC)
  have hpool_sC : A.pool lim st s = A.pool lim st sC :=
    (A.pool_transport lim st s sC hvm_sC).symm
  have hPC' : PC ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      A.pool lim st sC ∗
      (epilogueOutFull out
        (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
        (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
        (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
        ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
        (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
        (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
        (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
        w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
        (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
        (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
        (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
        (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
        w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240 q1888 q1904 w1920 ∗
       Frame) := by
    refine Entails.trans hPC ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    have hstk := epilogueStackPost_entails_2304 (s0.sp - 2400#64)
      d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240 hbs240
      q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 q1888 q1904 w1920
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hstk))
    rw [hpool_sC]
    unfold epilogueStackPartBPost epilogueStackGaps
      epilogueOutPartANo145 epilogueOutPartBPost epilogueOutFull
    exact Entails.of_eq (by sep_ac_rfl)
  have hep := DefsBudget.states_from_pb_epilogue_64_placed (ext := ext) A lim st s0 sC
    (epilogueOutFull out
      (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
      (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
      (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
      ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
      (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
      (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
      (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
      w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
      (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
      q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
      (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
      (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
      (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
      w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
      bs240 q1888 q1904 w1920 ∗
     Frame)
    halign hpcC hrunC hspC (htrC.trans (htrB.trans (htrA.trans htr)))
  refine SepWP.weaken_pre hPC' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f, hvm_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f, hvm_sC.trans hvm_f⟩

private theorem epilogue_step_8176_8180_placed_raw [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (P_pre : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 8176#64)
    (hrun : s.status = .Running) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s P_pre
      (fun s1 P1 =>
        (P1 ⊢ P_pre) ∧ s1.sp = s.sp ∧ s1.readReg64 .x6 = s.sp + 576#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg32 .x3 = s.readReg32 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x4 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x7 = s.readReg64 .x7 ∧ s1.readReg64 .x8 = s.readReg64 .x8 ∧
        s1.readReg64 .x9 = s.readReg64 .x9 ∧ s1.readReg64 .x10 = s.readReg64 .x10 ∧
        s1.readReg64 .x11 = s.readReg64 .x11 ∧ s1.readReg64 .x12 = s.readReg64 .x12 ∧
        s1.readReg64 .x13 = s.readReg64 .x13 ∧ s1.readReg64 .x14 = s.readReg64 .x14 ∧
        s1.readReg64 .x15 = s.readReg64 .x15 ∧ s1.readReg64 .x16 = s.readReg64 .x16 ∧
        s1.readReg64 .x17 = s.readReg64 .x17 ∧ s1.readReg64 .x18 = s.readReg64 .x18 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg32 .x21 = s.readReg32 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg32 .x27 = s.readReg32 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved s1 s) := by
  change s.pc = (blkPl_333).base + 8176#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 8180#64) s P_pre _
  wp_steps; wp_done

private theorem epilogue_step_8176_8180_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (P_pre : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 8176#64)
    (hrun : s.status = .Running) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8180#64) s P_pre
      (fun s1 P1 =>
        (P1 ⊢ P_pre) ∧ VmPreserved s s1 ∧ s1.sp = s.sp ∧ s1.readReg64 .x6 = s.sp + 576#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg32 .x3 = s.readReg32 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x4 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x7 = s.readReg64 .x7 ∧ s1.readReg64 .x8 = s.readReg64 .x8 ∧
        s1.readReg64 .x9 = s.readReg64 .x9 ∧ s1.readReg64 .x10 = s.readReg64 .x10 ∧
        s1.readReg64 .x11 = s.readReg64 .x11 ∧ s1.readReg64 .x12 = s.readReg64 .x12 ∧
        s1.readReg64 .x13 = s.readReg64 .x13 ∧ s1.readReg64 .x14 = s.readReg64 .x14 ∧
        s1.readReg64 .x15 = s.readReg64 .x15 ∧ s1.readReg64 .x16 = s.readReg64 .x16 ∧
        s1.readReg64 .x17 = s.readReg64 .x17 ∧ s1.readReg64 .x18 = s.readReg64 .x18 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg32 .x21 = s.readReg32 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg32 .x27 = s.readReg32 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved s1 s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (epilogue_step_8176_8180_placed_raw (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      P_pre (by simpa using hpc) (by simpa using hrun))
    fun s1 P1 hvm
      ⟨hP1, hsp1, hx6, hx0, hx1, hx2, hx3, hx4, hx5, hx7, hx8, hx9, hx10, hx11, hx12,
       hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25,
       hx26, hx27, hx27_32, hx28, hx30, htr1⟩ => by
      exact ⟨hP1, hvm, by simpa using hsp1, by simpa using hx6,
        by simpa using hx0, by simpa using hx1, by simpa using hx2, by simpa using hx3,
        by simpa using hx4, by simpa using hx5, by simpa using hx7, by simpa using hx8,
        by simpa using hx9, by simpa using hx10, by simpa using hx11, by simpa using hx12,
        by simpa using hx13, by simpa using hx14, by simpa using hx15, by simpa using hx16,
        by simpa using hx17, by simpa using hx18, by simpa using hx19, by simpa using hx20,
        by simpa using hx21, by simpa using hx22, by simpa using hx23, by simpa using hx24,
        by simpa using hx25, by simpa using hx26, by simpa using hx27, by simpa using hx27_32,
        by simpa using hx28, by simpa using hx30,
        ⟨by simpa using htr1.1, by simpa using htr1.2⟩⟩

/-- Relocatable complete shared `Ok` epilogue from `+8176` (`add x6, sp, #576`) to `s0.x30`
    in Block `333`, threading `A.pool lim st` and `VmPreserved`. -/
theorem states_from_pb_epilogue_8176_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (out : BitVec 64)
    (d92 d172 : BitVec 32) (w104 w112 w120 w160 w192 w208 w224 w232 : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (q576 : BitVec 128) (w592 : BitVec 64)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 : BitVec 128)
    (w832 : BitVec 64) (q848 : BitVec 128) (w864 w880 w888 : BitVec 64)
    (q1888 q1904 : BitVec 128) (w1920 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8176#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       epilogueStackSlots (s0.sp - 2400#64)
         d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
         q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
         w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
       epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame ∗
       A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutFull out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
            w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
            (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
            q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
            w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
            w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
            bs240 q1888 q1904 w1920 ∗
          stackAt s0.sp statesFromPbStack ∗ Frame ∗ A.pool lim st sm) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace ∧
        VmPreserved s sm) := by
  refine SepWP.seq (epilogue_step_8176_8180_placed (ext := ext) s _ hpc hrun) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hvm1, hsp1, hx6_1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx7_1,
    hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
    hx28_1, hx30_1, htr1⟩
  have hP1' : P1 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64)
        d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240
        q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
        w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗ Frame ∗
      A.pool lim st s1 := by
    rw [A.pool_transport lim st s s1 hvm1]
    exact hP1
  have hep := states_from_pb_epilogue_8180_placed A lim st hmemcpy_ok s0 s1 out
    d92 d172 w104 w112 w120 w160 w192 w208 w224 w232 bs240 hbs240
    q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame
    halign hpc1 hrun1 (hsp1.trans hsp) (hx6_1.trans (congrArg (· + 576#64) hsp))
    (hx19_1.trans hx19) (hx23_1.trans hx23) (htr1.trans htr)
  rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
      hx3_1, hx27_32_1, hx27_1, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1,
      hx10_1, hx26_1, hx12_1, hx1_1, hx28_1, hx16_1] at hep
  refine SepWP.weaken_pre hP1' (SepWP.mono hep ?_)
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m, hvm2⟩
  exact ⟨hPm, hsp_m, hcc_m, htr_m, hvm1.trans hvm2⟩

theorem states_from_pb_epilogue_8176_keysUnsampled_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ "memcpy") allocMemcpyVmSpec)
    (s0 s : State) (out pa1 : BitVec 64) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8176#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion (s0.sp - 2400#64) 208 ∗ ((s0.sp - 2400#64 + 208#64) ↦₆₄ pa1) ∗
       memRegion (s0.sp - 2400#64 + 216#64) 2088 ∗ statesFromPbSavedCells s0 ∗
       Frame ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          (out ↦₆₄ s.readReg64 .x8) ∗ ((out + 8#64) ↦₆₄ s.readReg64 .x15) ∗
          ((out + 16#64) ↦₆₄ pa1) ∗ ((out + 24#64) ↦₆₄ s.readReg64 .x20) ∗
          ((out + 32#64) ↦₆₄ s.readReg64 .x13) ∗ ((out + 40#64) ↦₆₄ s.readReg64 .x25) ∗
          ((out + 48#64) ↦₆₄ s.readReg64 .x30) ∗ ((out + 56#64) ↦₆₄ s.readReg64 .x9) ∗
          memRegion (out + 64#64) 864 ∗ stackAt s0.sp statesFromPbStack ∗
          Frame ∗ A.pool lim st sm) ∧
        sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace ∧
        VmPreserved s sm) := by
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (memRegion_208_entails_epilogue_lo (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono_left (memRegion_2088_entails_epilogue_hi (s0.sp - 2400#64))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun w1920 => ProofLib.SepWP.exists_left fun q1904 =>
    ProofLib.SepWP.exists_left fun q1888 => ProofLib.SepWP.exists_left fun w888 =>
    ProofLib.SepWP.exists_left fun w880 => ProofLib.SepWP.exists_left fun w864 =>
    ProofLib.SepWP.exists_left fun q848 => ProofLib.SepWP.exists_left fun w832 =>
    ProofLib.SepWP.exists_left fun q816 => ProofLib.SepWP.exists_left fun q800 =>
    ProofLib.SepWP.exists_left fun q784 => ProofLib.SepWP.exists_left fun q768 =>
    ProofLib.SepWP.exists_left fun q752 => ProofLib.SepWP.exists_left fun q736 =>
    ProofLib.SepWP.exists_left fun q720 => ProofLib.SepWP.exists_left fun q704 =>
    ProofLib.SepWP.exists_left fun q688 => ProofLib.SepWP.exists_left fun q672 =>
    ProofLib.SepWP.exists_left fun q656 => ProofLib.SepWP.exists_left fun q640 =>
    ProofLib.SepWP.exists_left fun q624 => ProofLib.SepWP.exists_left fun q608 =>
    ProofLib.SepWP.exists_left fun w592 => ProofLib.SepWP.exists_left fun q576 =>
    ProofLib.SepWP.exists_left fun bs240 => ProofLib.SepWP.exists_left fun w232 =>
    ProofLib.SepWP.exists_left fun w224 => ProofLib.SepWP.exists_left fun w192 =>
    ProofLib.SepWP.exists_left fun d172 => ProofLib.SepWP.exists_left fun w160 =>
    ProofLib.SepWP.exists_left fun w120 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d92 => ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
    epilogueStackSlots (s0.sp - 2400#64) d92 d172 w104 w112 w120 w160 w192 pa1 w224 w232 bs240.val
      q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
      w832 q848 w864 w880 w888 q1888 q1904 w1920 ∗
    epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
    Frame ∗ A.pool lim st s by
      unfold epilogueStackSlots epilogueStackGaps; sep_ac_rfl)) ?_
  refine SepWP.mono (states_from_pb_epilogue_8176_placed A lim st hmemcpy_ok s0 s out
    d92 d172 w104 w112 w120 w160 w192 pa1 w224 w232 bs240.val bs240.property
    q576 w592 q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888 q1888 q1904 w1920 Frame halign hpc hrun hsp hx19 hx23 htr) ?_
  intro sm Pm _ _ ⟨hPm, hsp_m, hcc_m, htr_m, hvm_m⟩
  refine ⟨Entails.trans hPm (Entails.trans (sepConj_mono_left (epilogueOutFull_entails_64_864 out
    (s.readReg64 .x8) (s.readReg64 .x15) pa1 (s.readReg64 .x20)
    (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
    (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
    ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
    (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
    (((s.readReg64 .x27 >>> 48).setWidth 32).setWidth 8)
    (s.readReg64 .x4) (s.readReg64 .x5) ((s.readReg32 .x21).setWidth 8)
    w880 (overlapWord7 w880 w888) (s.readReg64 .x7)
    (d172.setWidth 8) q848 (overlapWord7 (q848.extractLsb' 64 64) w864)
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 (s.readReg64 .x2) (s.readReg64 .x11) (s.readReg64 .x22)
    (s.readReg64 .x24) w232 (s.readReg64 .x10) w160
    (s.readReg64 .x26) (s.readReg64 .x12) (s.readReg64 .x1) w224
    (s.readReg64 .x28) w192 (s.readReg64 .x16) w104
    w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
    bs240.val bs240.property q1888 q1904 w1920)) (Entails.of_eq (by sep_ac_rfl))),
    hsp_m, hcc_m, htr_m, hvm_m⟩

/-! ## `KeysUnsampled` Error Leaves (`uc = none`, `auth = none`) & Entry Unpack (`+156 -> +200`) -/

/-- Budget-threaded `uc = none` error path (`+156 -> +2044 -> ret`) in Block `333`. -/
theorem states_from_pb_keysUnsampled_uc_none_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ none2Cap) ∗
        memRegion (pbA + 16#64) 48 ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := none }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool lim st sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        VmPreserved s1 sf) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant1bPlaced.states_from_pb_keysUnsampled_uc_none_placed
      (A := A.atState lim st s1) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ => by
      have hres :
          resultChunkedStatesAt (A.atState lim st s1) (F := F) out
            (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := none }) }) =
          resultChunkedStatesAt A.repAlloc (F := F) out
            (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := none }) }) := rfl
      rw [hres, LibsignalBinary.Heap.RustCliAllocBudget.atState_pool, ← A.pool_transport lim st s1 sf hvm] at hPf
      exact ⟨hPf, by simpa using hsp_f, by simpa [CalleeSavedPreserved] using hcc_f,
        by simpa using htr_f, hvm⟩

/-- Budget-threaded `auth = none` error path (`+156 -> +2044 -> ret`) in Block `333`. -/
theorem states_from_pb_keysUnsampled_auth_none_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA ep : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 156#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000000#64) ∗ ((pbA + 8#64) ↦₆₄ noneCap) ∗
        memRegion (pbA + 16#64) 40 ∗ ((pbA + 56#64) ↦₆₄ ep) ∗ memRegion (pbA + 64#64) 160 ∗
        statesFromPbJumpTablePlacedAt ∗ A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out
            (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := none, epoch := ep } }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool lim st sf ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace ∧
        VmPreserved s1 sf) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant1bPlaced.states_from_pb_keysUnsampled_auth_none_placed
      (A := A.atState lim st s1) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out pbA ep hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ => by
      have hres :
          resultChunkedStatesAt (A.atState lim st s1) (F := F) out
            (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := none, epoch := ep } }) }) =
          resultChunkedStatesAt A.repAlloc (F := F) out
            (CryptoVerification.LibsignalSpqrV1.States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.keysUnsampled { uc := some { auth := none, epoch := ep } }) }) := rfl
      rw [hres, LibsignalBinary.Heap.RustCliAllocBudget.atState_pool, ← A.pool_transport lim st s1 sf hvm] at hPf
      exact ⟨hPf, by simpa using hsp_f, by simpa [CalleeSavedPreserved] using hcc_f,
        by simpa using htr_f, hvm⟩

theorem states_from_pb_keysUnsampled_step0_156_200_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ep w152 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Frame : SepProp)
    (hcap0 : ga.rootKey.cap.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 200#64) s
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗
        authenticatorPBPinnedAt A ga (pbA + 8#64) auth ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗
        memRegion (pbA + 64#64) 160 ∗
        ((fsp + 152#64) ↦₆₄ w152) ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 152#64) ↦₆₄ ep) ∗
          vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
          vecU8Payload A ga.macKey.cap ga.macKey.ptr auth.macKey ∗
          memRegion pbA optProtoInnerStateSize ∗ Frame) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧
        s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧
        s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
        TraceCalleeSaved s1 s ∧
        VmPreserved s s1) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant1bPlaced.states_from_pb_keysUnsampled_step0_156_200_placed
      (A := A) (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out pbA ep w152 ga auth Frame hcap0 hfsp_align
      (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx19) (by simpa using hx23) (by simpa using hx27))
    fun s1 P1 hvm
      ⟨hP1, hsp1, hx19_1, hx23_1, hx22_1, hx24_1, hx20_1, hx21_1, hx26_1, hx13_1, hx27_1, htr1⟩ =>
      ⟨hP1, hsp1, hx19_1, hx23_1, hx22_1, hx24_1, hx20_1, hx21_1, hx26_1, hx13_1, hx27_1,
        ⟨by simpa using htr1.1, by simpa using htr1.2⟩, hvm⟩

theorem states_from_pb_keysUnsampled_step0_156_200_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out pbA ep w152 : BitVec 64)
    (ga : AuthenticatorPBGhost) (auth : ProtoAuthenticator)
    (Frame : SepProp)
    (hcap0 : ga.rootKey.cap.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx27 : s.readReg64 .x27 = pbA) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333 + 200#64) s
      ((pbA ↦₆₄ 0x8000000000000000#64) ∗
        authenticatorPBPinnedAt A.repAlloc ga (pbA + 8#64) auth ∗
        ((pbA + 56#64) ↦₆₄ ep) ∗
        memRegion (pbA + 64#64) 160 ∗
        ((fsp + 152#64) ↦₆₄ w152) ∗ Frame ∗ A.pool lim st s)
      (fun s1 P1 =>
        (P1 ⊢
          ((fsp + 152#64) ↦₆₄ ep) ∗
          vecU8Payload A.repAlloc ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
          vecU8Payload A.repAlloc ga.macKey.cap ga.macKey.ptr auth.macKey ∗
          memRegion pbA optProtoInnerStateSize ∗ Frame ∗ A.pool lim st s1) ∧
        s1.sp = fsp ∧
        s1.readReg64 .x19 = out ∧
        s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x22 = ga.rootKey.cap ∧
        s1.readReg64 .x24 = ga.rootKey.ptr ∧
        s1.readReg64 .x20 = ga.macKey.cap ∧
        s1.readReg64 .x21 = ga.macKey.ptr ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 auth.rootKey.length ∧
        s1.readReg64 .x13 = BitVec.ofNat 64 auth.macKey.length ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 auth.macKey.length ∧
        TraceCalleeSaved s1 s ∧
        VmPreserved s s1) := by
  have h := states_from_pb_keysUnsampled_step0_156_200_placed (A := A.repAlloc) (ext := ext)
    s fsp out pbA ep w152 ga auth (Frame ∗ A.pool lim st s)
    hcap0 hfsp_align hpc hrun hsp hx19 hx23 hx27
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono h ?_)
  intro s1 P1 _ _ ⟨hP1, hrest⟩
  have hvm : VmPreserved s s1 := hrest.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨Entails.trans hP1 ?_, hrest⟩
  rw [A.pool_transport lim st s s1 hvm]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux
