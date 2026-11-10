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
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Shared `Ok` and `Err` Epilogues (Block `333`)

Proves `VmPreserved`-strengthened and `RustCliAllocBudget M` pool-threading relocatable shared
`Ok` (`+8180 -> +8284 -> +8468 -> +64`) and `Err` (`+60`, `+2044`, `+2048`) epilogue theorems for
Block `333`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (Error)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved bv328_toNat epilogueOutPartA epilogueOutPartBPost epilogueOutPartBPre
   epilogueStackPartA epilogueStackPartBPost epilogueStackPartBPre fsp_576_add_15 fsp_848_add_15
   fsp_848_add_39 out_121_add_8 out_145_add_15 out_168_add_128 out_168_add_128_16 out_168_add_160
   out_168_add_160_16 out_168_add_192 out_168_add_192_16 out_168_add_96 out_168_add_96_16
   out_537_add_16 out_537_add_8 out_888_add_16 out_888_add_8 out_904_add_8 overlapWord7
   resultChunkedStatesAt spqrErrorByte statesFromPbSavedCells statesFromPbStack)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
  (sessionMemcpyVmAcpSpec subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local arm64_norm, local wp_norm]
  out_168_add_96 out_168_add_96_16 out_168_add_128 out_168_add_128_16
  out_168_add_160 out_168_add_160_16 out_168_add_192 out_168_add_192_16
  out_888_add_8 out_888_add_16 out_904_add_8
  fsp_848_add_15 fsp_848_add_39 fsp_576_add_15
  out_537_add_8 out_537_add_16 out_145_add_15 out_121_add_8
  bv328_toNat

@[local simp] private theorem stripS_readReg32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

alias states_from_pb_epilogue_64_placed := DefsBudget.states_from_pb_epilogue_64_placed

/-! ## 1. Relocatable Shared `Ok` Epilogue Steps (`+8180 -> +8284 -> +8468 -> +64`) -/

/-- `VmPreserved`-strengthened Step A of the shared `Ok` epilogue (`+8180 -> +8284`, Block `333`). -/
theorem epilogue_step_8180_8284_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 : BitVec 64)
    (ub96 : BitVec 8) (ud97 : BitVec 32) (uh101 : BitVec 16)
    (uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376 : BitVec 128)
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
      (epilogueOutPartA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88
         ub96 ud97 uh101 uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376 ∗
       epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutPartA out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            q848 q704 q720 q736 q752 q768 q784 q800 q816 ∗
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
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.epilogue_step_8180_8284_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88
      ub96 ud97 uh101 uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376
      w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 Frame
      hfsp_align (by simpa using hpc) (by simpa using hrun)
      (by simpa using hsp) (by simpa using hx19))
    fun sm Pm hvm
      ⟨hPm, hsp_m, hx0, hx1, hx2, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx16,
       hx19_m, hx21, hx22, hx23, hx24, hx26, hx28, hx29, htr_m⟩ => by
      simp only [stripS_readReg64, stripS_readReg32] at hPm
      exact ⟨hPm, hvm, hsp_m, hx0, by simpa using hx1, by simpa using hx2,
        by simpa using hx4, by simpa using hx5, by simpa using hx6, by simpa using hx7,
        by simpa using hx8, hx9, by simpa using hx10, by simpa using hx11,
        by simpa using hx12, by simpa using hx16, hx19_m, by simpa using hx21,
        by simpa using hx22, by simpa using hx23, by simpa using hx24,
        by simpa using hx26, by simpa using hx28, by simpa using hx29,
        ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem epilogue_step_8180_8284_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 : BitVec 64)
    (ub96 : BitVec 8) (ud97 : BitVec 32) (uh101 : BitVec 16)
    (uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376 : BitVec 128)
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
      (epilogueOutPartA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88
         ub96 ud97 uh101 uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376 ∗
       epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
       Frame ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutPartA out
            (s.readReg64 .x8) (s.readReg64 .x15) w208 (s.readReg64 .x20)
            (s.readReg64 .x13) (s.readReg64 .x25) (s.readReg64 .x30) (s.readReg64 .x9)
            (s.readReg64 .x14) (s.readReg64 .x18) (s.readReg64 .x17) (s.readReg64 .x0)
            ((s.readReg32 .x3).setWidth 8) (s.readReg32 .x27)
            (((s.readReg64 .x27 >>> 32).setWidth 32).setWidth 16)
            q848 q704 q720 q736 q752 q768 q784 q800 q816 ∗
          epilogueStackPartA fsp w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848 ∗
          Frame ∗ A.pool lim st sm) ∧
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
  have hwp := epilogue_step_8180_8284_placed (ext := ext)
    s fsp out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88
    ub96 ud97 uh101 uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376
    w208 w880 q704 q720 q736 q752 q768 q784 q800 q816 q848
    (Frame ∗ A.pool lim st s) hfsp_align hpc hrun hsp hx19
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-- `VmPreserved`-strengthened Step B of the shared `Ok` epilogue (`+8284 -> +8468`, Block `333`). -/
theorem epilogue_step_8284_8468_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (ub103 : BitVec 8) (u104 u112 : BitVec 64) (ub120 : BitVec 8)
    (u121 u128 u136 : BitVec 64) (ub144 : BitVec 8) (u160 : BitVec 64)
    (uq168 uq184 uq200 uq216 uq232 uq248 : BitVec 128)
    (u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528 : BitVec 64)
    (ub536 : BitVec 8) (u537 u545 u552 : BitVec 64)
    (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887 : BitVec 64)
    (q576 q608 q624 q640 q656 q672 q688 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx6 : s.readReg64 .x6 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8468#64)
      s
      (epilogueOutPartBPre out ub103 u104 u112 ub120 u121 u128 u136 ub144 u160
         uq168 uq184 uq200 uq216 uq232 uq248
         u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528
         ub536 u537 u545 u552 ∗
       epilogueStackPartBPre fsp d92 d172
         w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
         q576 q608 q624 q640 q656 q672 q688 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutPartBPost out
            ((s.readReg32 .x8).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5)
            ((s.readReg32 .x21).setWidth 8)
            (s.readReg64 .x9) w887 (s.readReg64 .x7)
            (d172.setWidth 8) w863
            q608 q624 q640 q656 q672 q688
            w832 (s.readReg64 .x2)
            (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232
            (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12)
            (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192
            (s.readReg64 .x16) w104
            w112 w120
            (d92.setWidth 8) q576
            (overlapWord7 (q576.extractLsb' 64 64) w592) ∗
          epilogueStackPartBPost fsp d92 d172
            w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
            q576 q608 q624 q640 q656 q672 q688 ∗
          Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 560#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x2 = 328#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.epilogue_step_8284_8468_placed
      (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out ub103 u104 u112 ub120 u121 u128 u136 ub144 u160
      uq168 uq184 uq200 uq216 uq232 uq248
      u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528
      ub536 u537 u545 u552 d92 d172
      w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
      q576 q608 q624 q640 q656 q672 q688 Frame
      hfsp_align (by simpa using hpc) (by simpa using hrun) (by simpa using hsp)
      (by simpa using hx0) (by simpa using hx6) (by simpa using hx19) (by simpa using hx23))
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx2_m, hx19_m, hx29_m, htr_m⟩ => by
      simp only [stripS_readReg64, stripS_readReg32] at hPm
      exact ⟨hPm, hvm, hsp_m, hx0_m, hx1_m, hx2_m, hx19_m,
        by simpa using hx29_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem epilogue_step_8284_8468_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (ub103 : BitVec 8) (u104 u112 : BitVec 64) (ub120 : BitVec 8)
    (u121 u128 u136 : BitVec 64) (ub144 : BitVec 8) (u160 : BitVec 64)
    (uq168 uq184 uq200 uq216 uq232 uq248 : BitVec 128)
    (u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528 : BitVec 64)
    (ub536 : BitVec 8) (u537 u545 u552 : BitVec 64)
    (d92 d172 : BitVec 32)
    (w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887 : BitVec 64)
    (q576 q608 q624 q640 q656 q672 q688 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx6 : s.readReg64 .x6 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 8468#64)
      s
      (epilogueOutPartBPre out ub103 u104 u112 ub120 u121 u128 u136 ub144 u160
         uq168 uq184 uq200 uq216 uq232 uq248
         u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528
         ub536 u537 u545 u552 ∗
       epilogueStackPartBPre fsp d92 d172
         w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
         q576 q608 q624 q640 q656 q672 q688 ∗
       Frame ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          epilogueOutPartBPost out
            ((s.readReg32 .x8).setWidth 8)
            (s.readReg64 .x4) (s.readReg64 .x5)
            ((s.readReg32 .x21).setWidth 8)
            (s.readReg64 .x9) w887 (s.readReg64 .x7)
            (d172.setWidth 8) w863
            q608 q624 q640 q656 q672 q688
            w832 (s.readReg64 .x2)
            (s.readReg64 .x11) (s.readReg64 .x22)
            (s.readReg64 .x24) w232
            (s.readReg64 .x10) w160
            (s.readReg64 .x26) (s.readReg64 .x12)
            (s.readReg64 .x1) w224
            (s.readReg64 .x28) w192
            (s.readReg64 .x16) w104
            w112 w120
            (d92.setWidth 8) q576
            (overlapWord7 (q576.extractLsb' 64 64) w592) ∗
          epilogueStackPartBPost fsp d92 d172
            w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
            q576 q608 q624 q640 q656 q672 q688 ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 560#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x2 = 328#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  have hwp := epilogue_step_8284_8468_placed (ext := ext)
    s fsp out ub103 u104 u112 ub120 u121 u128 u136 ub144 u160
    uq168 uq184 uq200 uq216 uq232 uq248
    u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 u488 u496 u504 u512 u520 u528
    ub536 u537 u545 u552 d92 d172
    w104 w112 w120 w160 w192 w224 w232 w592 w832 w863 w887
    q576 q608 q624 q640 q656 q672 q688 (Frame ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx0 hx6 hx19 hx23
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

private theorem epilogue_step_8472_64_placed_raw [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64)
      s
      (((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗
          ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  change s.pc = (blkPl_333).base + 8472#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 64#64) s _ _
  wp_simp_pre [pointsTo128, sepConj_assoc]
  wp_steps
  simp only [pointsTo128, sepConj_assoc]
  wp_done

/-- `VmPreserved`-strengthened pure tail of Step C (`+8472 -> +64`, 7 instructions in Block `333`). -/
theorem epilogue_step_8472_64_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8472#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64)
      s
      (((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗
          ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗
          Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (epilogue_step_8472_64_placed_raw (ext := vmTrapHooks)
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s)
      fsp out uq888 uq904 q1888 q1904 u920 w1920 Frame
      hfsp_align (by simpa using hpc) (by simpa using hrun)
      (by simpa using hsp) (by simpa using hx19))
    fun sm Pm hvm ⟨hPm, hsp_m, htr_m⟩ =>
      ⟨hPm, hvm, hsp_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

/-- `VmPreserved`-strengthened Step C of the shared `Ok` epilogue (`+8468 -> +64`, 8 instructions
    including `BL memcpy`) under `allocMemcpyVmSpec`. -/
theorem epilogue_step_8468_64_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_ok :
      subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsρ "memcpy") allocMemcpyVmSpec)
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 560#64) 328 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗
       ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 560#64) ↦ₛ bs240) ∗
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗
          ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗
          ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗
          Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  have hmemcpy :
      subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        (lsρ "memcpy") (sessionMemcpyVmAcpSpec allocHookStack) :=
    subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm allocHookStack hmemcpy_ok
  simp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  refine SepWP.seq
    (mid := lsmpl.base 333 + 8472#64)
    (Mid := fun s1 P1 =>
      (P1 ⊢
        ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
        ((out + 920#64) ↦₆₄ u920) ∗
        ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
        ((fsp + 1920#64) ↦₆₄ w1920) ∗
        (stackAt fsp 4096 ∗ ((out + 560#64) ↦ₛ bs240) ∗ ((fsp + 240#64) ↦ₛ bs240) ∗ Frame)) ∧
      VmPreserved s s1 ∧
      s1.sp = fsp ∧
      s1.readReg64 .x19 = out ∧
      TraceCalleeSaved s1 s) ?_ ?_
  · subst hsp hx19
    rw [← hbs240]
    change s.pc = (blkPl_333).base + 8468#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8472#64) s _ _
    wp_steps 1
    wp_call hmemcpy (s.readReg64 .x19 + 560#64, s.sp + 240#64, bs240)
    have hvm_mc : VmPreserved s sf := by
      simpa [VmPreserved, LibsignalBinary.Heap.PoolPreserved, LibsignalBinary.Heap.FdsHiFrame,
        wp_norm, arm64_norm] using hpost
    apply SepWP.done hpc_sf hrun_sf
    refine ⟨?_, hvm_mc, hsp_sf, by dsimp only [Reg.x19]; assumption, ⟨by assumption, hvregs⟩⟩
    simp only [wp_norm, arm64_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 _P1 hpc1 hrun1 ⟨hP1, hvm1, hsp1, hx19_1, htr1⟩
    refine SepWP.weaken_pre hP1 ?_
    have hstep2 := epilogue_step_8472_64_placed (ext := ext)
      s1 fsp out uq888 uq904 q1888 q1904 u920 w1920
      (stackAt fsp 4096 ∗ ((out + 560#64) ↦ₛ bs240) ∗ ((fsp + 240#64) ↦ₛ bs240) ∗ Frame)
      hfsp_align hpc1 hrun1 hsp1 hx19_1
    refine SepWP.mono hstep2 fun sm _Pm _ _ ⟨hPm2, hvm2, hspm, htr2⟩ => ?_
    refine ⟨Entails.trans hPm2 (Entails.of_eq (by sep_ac_rfl)),
      hvm1.trans hvm2, hspm, ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩⟩

theorem epilogue_step_8468_64_placed_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : DefsBudget.FromPbAllocHooksPlacedBudget M A lim ext)
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 560#64) 328 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗
       ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 560#64) ↦ₛ bs240) ∗
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗
          ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗
          ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗
          Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) :=
  epilogue_step_8468_64_placed hA.memcpy_ok s fsp out bs240 hbs240
    uq888 uq904 q1888 q1904 u920 w1920 Frame
    hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19

theorem epilogue_step_8468_64_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (hA : DefsBudget.FromPbAllocHooksPlacedBudget M A lim ext)
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 64#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 560#64) 328 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗
       ((fsp + 240#64) ↦ₛ bs240) ∗
       ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
       ((fsp + 1920#64) ↦₆₄ w1920) ∗
       Frame ∗ A.pool lim st s)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 560#64) ↦ₛ bs240) ∗
          ((out + 888#64) ↦₁₂₈ q1888) ∗ ((out + 904#64) ↦₁₂₈ q1904) ∗
          ((out + 920#64) ↦₆₄ w1920) ∗
          ((fsp + 240#64) ↦ₛ bs240) ∗
          ((fsp + 1888#64) ↦₁₂₈ q1888) ∗ ((fsp + 1904#64) ↦₁₂₈ q1904) ∗
          ((fsp + 1920#64) ↦₆₄ w1920) ∗
          Frame ∗ A.pool lim st sm) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  have hwp := epilogue_step_8468_64_placed hA.memcpy_ok s fsp out bs240 hbs240
    uq888 uq904 q1888 q1904 u920 w1920 (Frame ∗ A.pool lim st s)
    hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## 2. Relocatable Shared Error Epilogues (`+60`, `+2044`, `+2048`) -/

/-- `VmPreserved`-strengthened relocatable shared `Err(err)` epilogue from `+60` (`+60 -> s0.x30`). -/
theorem states_from_pb_epilogue_60_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (v0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = noneCap)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        (out ↦₆₄ v0) ∗
        ((out + 8#64) ↦₈ spqrErrorByte err) ∗
        memRegion (out + 9#64) 919 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.states_from_pb_epilogue_60_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err v0 Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx8_1) (by simpa using hx19_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem states_from_pb_epilogue_60_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (v0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = noneCap)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        (out ↦₆₄ v0) ∗
        ((out + 8#64) ↦₈ spqrErrorByte err) ∗
        memRegion (out + 9#64) 919 ∗
        Rest ∗ A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          Rest ∗ A.pool lim st sf ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := states_from_pb_epilogue_60_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err v0 (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx8_1 hx19_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened relocatable shared `Err(err)` exit at `+2048` (`+2048 -> s0.x30`). -/
theorem states_from_pb_err_2048_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2048#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx9_1 : (s1.readReg64 .x9).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.states_from_pb_err_2048_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out err Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1) (by simpa using hx9_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem states_from_pb_err_2048_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2048#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx9_1 : (s1.readReg64 .x9).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest ∗ A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err err)) ∗
          Rest ∗ A.pool lim st sf ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := states_from_pb_err_2048_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out err (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx9_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

/-- `VmPreserved`-strengthened relocatable shared `Err(Error::StateDecode)` exit at `+2044`. -/
theorem states_from_pb_err_2044_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2044#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (_root_.LibsignalBinary.Proofs.SpqrV1.States.FromPb.states_from_pb_err_2044_placed
      (A := A) (F := F) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      out Rest hsp0_align
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx19_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sf Pf hvm ⟨hPf, hsp_f, hcc_f, htr_f⟩ =>
      ⟨hPf, hvm, hsp_f, hcc_f, htr_f⟩

theorem states_from_pb_err_2044_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 2044#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest ∗ A.pool lim st s1)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A.repAlloc (F := F) out (.error (.err .stateDecode)) ∗
          Rest ∗ A.pool lim st sf ∗
          stackAt s0.sp statesFromPbStack) ∧
        VmPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwp := states_from_pb_err_2044_placed (A := A.repAlloc) (F := F) (ext := ext)
    s0 s1 out (Rest ∗ A.pool lim st s1)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 htr1
  refine SepWP.mono hwp fun sf Pf _ _ ⟨hPf, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPf
  exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlacedBudget
