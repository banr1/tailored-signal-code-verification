/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
public meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
meta import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Shared `Ok` and `Err` Epilogues for `<States>::from_pb`

Proves `VmPreserved`- and `AllocCallPreserved`-preserving shared `Ok` (`+8180 -> +8284 -> +8468 -> +64`)
and `Err` (`+60`, `+2044`, `+2048`) epilogue theorems for `<spqr::v1::chunked::states::States>::from_pb`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet (
  contractProg sessionMemcpySpec tripleRatchetProgAtExt
)
open CryptoVerification.SpqrV1.Drop (chunkedStatesSize)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (
  align_pre encoderFromPbStack loBytes7
)
open CryptoVerification.SpqrV1.Unchunked (
  extractLsb'_0_64_append extractLsb'_64_64_append
)
open CryptoVerification.SpqrV1.Layout.Stubs (stubOff_memcpy)
open CryptoVerification.SpqrV1.States.FromPb (
  TraceCalleeSaved bv328_toNat bv_add_lit_add_lit
  epilogueOutPartA epilogueOutPartBPost epilogueOutPartBPre
  epilogueStackPartA epilogueStackPartBPost epilogueStackPartBPre
  fsp_576_add_15 fsp_584_realign_rest fsp_848_add_15 fsp_848_add_39
  memRegion_out_928_split_32 out_121_add_8 out_121_realign_rest out_145_add_15
  out_168_add_128 out_168_add_128_16 out_168_add_160 out_168_add_160_16
  out_168_add_192 out_168_add_192_16 out_168_add_96 out_168_add_96_16
  out_537_add_16 out_537_add_8 out_545_realign_rest out_888_add_16 out_888_add_8
  out_8_32_entails_err_tail out_904_add_8 overlapWord7 resultChunkedStatesAt
  sp_sub_2400_add_2304 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_2304 spqrErrorByte
  stack_restore_statesFromPb statesFromPbName statesFromPbSavedCells
  statesFromPbStack statesFromPb_fnOff
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open scoped CryptoVerification.CodeLayout

open Lean Elab Tactic ProofLib ProofLib.ProgramReflection in
scoped elab "states_from_pb_fetches_range_b " b:term:max H:term:max k0:num len:num : tactic => do
  let off ← ProofLib.CodeLookup.lookupOff ``CryptoVerification.libsignalSessionCode "<spqr::v1::chunked::states::States>::from_pb"
  let offLit := Syntax.mkNumLit (toString off.val)
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.States.FromPb.statesFromPbBin $b $H statesFromPb_fnOff $offLit $k0 $len))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff stubOff_memcpy TraceCalleeSaved
attribute [local arm64_norm, local wp_norm]
  out_168_add_96 out_168_add_96_16 out_168_add_128 out_168_add_128_16
  out_168_add_160 out_168_add_160_16 out_168_add_192 out_168_add_192_16
  out_888_add_8 out_888_add_16 out_904_add_8
  fsp_848_add_15 fsp_848_add_39 fsp_576_add_15
  out_537_add_8 out_537_add_16 out_145_add_15 out_121_add_8 bv328_toNat
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64
  sp_sub_96_add_80 sp_sub_96_sub_2304 sp_sub_2400_add_2304

private theorem fnAddr_rebase_hooks_eq (P : Program) (b : BitVec 64)
    (h1 h2 : String → Option (State → State)) (name : String) :
    (P.rebase b h1).fnAddr name = (P.rebase b h2).fnAddr name := by
  unfold Program.fnAddr Program.fnOff; rfl

private theorem sepWP_swap_vm {prog : Program} {tgt : BitVec 64} {s : State}
    {Pre : SepProp} {Ent : SepProp → Prop} {Rest : State → Prop}
    (h : SepWP prog tgt s Pre (fun sm Pm => VmPreserved s sm ∧ Ent Pm ∧ Rest sm)) :
    SepWP prog tgt s Pre (fun sm Pm => Ent Pm ∧ VmPreserved s sm ∧ Rest sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hent, hr⟩ => ⟨hent, hvm, hr⟩

private theorem vmPreserved_of_step {s s' sf : State}
    (h2 : VmPreserved s' sf) (h1 : VmPreserved s s') : VmPreserved s sf :=
  h1.trans h2

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 1. Epilogue Return (`+64 -> s0.x30`) -/

/-- Budget-threaded epilogue (`+64 -> s0.x30`), proving `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem states_from_pb_epilogue_64 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 2400#64)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp statesFromPbStack ∗ Rest) ∧
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_from_pb_fetches_range_b b trapHooks 64 32
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  apply sepWP_swap_vm
  by_vm_steps {
    unfold statesFromPbSavedCells
    wp_steps
    have hrest := stack_restore_statesFromPb s0
    unfold statesFromPbSavedCells at hrest
    have hent :
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          ((((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
            ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
            ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
            ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
            ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
            ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ Rest) ⊢
        stackAt s0.sp statesFromPbStack ∗ Rest :=
      Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left hrest)
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by sep_ac_rfl)) hent) ?_
    wp_done
  }

/-! ## 2. Shared `Ok` Epilogue Steps (`+8180 -> +8284 -> +8468 -> +64`) -/

set_option maxHeartbeats 1200000 in
theorem epilogue_step_8180_8284
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 : BitVec 64)
    (ub96 : BitVec 8) (ud97 : BitVec 32) (uh101 : BitVec 16)
    (uq145 uq264 uq280 uq296 uq312 uq328 uq344 uq360 uq376 : BitVec 128)
    (w208 w880 : BitVec 64)
    (q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8284#64)
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
        AllocCallPreserved s sm ∧
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
  subst hsp hx19
  states_from_pb_fetches_range_b b trapHooks 8180 104
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  apply sepWP_swap_vm
  by_vm_steps {
    wp_simp_pre [epilogueOutPartA, epilogueStackPartA, pointsTo128, sepConj_assoc]
    wp_steps
    simp only [epilogueOutPartA, epilogueStackPartA, pointsTo128, sepConj_assoc]
    wp_done
  }

set_option maxHeartbeats 1600000 in
theorem epilogue_step_8284_8468
    {b : BitVec 64} {ext : String → Option (State → State)}
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
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx6 : s.readReg64 .x6 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out)
    (hx23 : s.readReg64 .x23 = fsp + 848#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8468#64)
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
        AllocCallPreserved s sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 560#64 ∧
        sm.readReg64 .x1 = fsp + 240#64 ∧
        sm.readReg64 .x2 = 328#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  states_from_pb_fetches_range_b b trapHooks 8284 184
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  apply sepWP_swap_vm
  by_vm_steps {
    wp_simp_pre [epilogueOutPartBPre, epilogueStackPartBPre, pointsTo128, sepConj_assoc]
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    wp_simp_pre [out_121_realign_rest]
    iterate 32 wp_step
    wp_simp_pre [fsp_584_realign_rest]
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    wp_simp_pre [out_545_realign_rest]
    wp_step
    simp only [epilogueOutPartBPost, epilogueStackPartBPost, pointsTo128, sepConj_assoc]
    wp_done
  }

/-- Budget-threaded Step C (`+8468 -> +64`, 8 instructions including `BL memcpy`). -/
theorem epilogue_step_8468_64
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (s : State) (fsp out : BitVec 64)
    (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328)
    (uq888 uq904 q1888 q1904 : BitVec 128) (u920 w1920 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 560#64)
    (hx1 : s.readReg64 .x1 = fsp + 240#64)
    (hx2 : s.readReg64 .x2 = 328#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64)
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
  subst hsp hx19
  have hmemcpy := hA.session_memcpy_ok_at statesFromPbName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
  simp only [withVmPreserved, sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  rw [← hbs240]
  refine SepWP.seq
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8472#64)
    (Mid := fun s1 P1 =>
      (P1 ⊢
        memRegion (s.sp - 4096#64) 4096 ∗
        ((s.readReg64 .x19 + 560#64) ↦ₛ bs240) ∗
        ((s.readReg64 .x19 + 888#64) ↦₁₂₈ uq888) ∗ ((s.readReg64 .x19 + 904#64) ↦₁₂₈ uq904) ∗
        ((s.readReg64 .x19 + 920#64) ↦₆₄ u920) ∗
        ((s.sp + 240#64) ↦ₛ bs240) ∗
        ((s.sp + 1888#64) ↦₁₂₈ q1888) ∗ ((s.sp + 1904#64) ↦₁₂₈ q1904) ∗
        ((s.sp + 1920#64) ↦₆₄ w1920) ∗
        Frame) ∧
      VmPreserved s s1 ∧
      s1.sp = s.sp ∧
      s1.readReg64 .x19 = s.readReg64 .x19 ∧
      TraceCalleeSaved s1 s) ?_ ?_
  · states_from_pb_fetches_range_b b (Rust.withPanics ext) 8468 4
    dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps 1
    wp_call hmemcpy (s.readReg64 .x19 + 560#64, s.sp + 240#64, bs240)
    have hvm_all : VmPreserved s sf :=
      vmPreserved_of_step (by assumption)
        (by simp [VmPreserved, LibsignalBinary.Heap.PoolPreserved, wp_norm, arm64_norm])
    apply SepWP.done hpc_sf hrun_sf
    refine ⟨?_, hvm_all, hsp_sf, by dsimp only [Reg.x19]; assumption, ⟨hpost, hvregs⟩⟩
    simp only [wp_norm, arm64_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s1 _P1 hpc1 hrun1 ⟨hP1, hvm1, hsp1, hx19_1, htr1⟩
    refine SepWP.weaken_pre hP1 ?_
    states_from_pb_fetches_range_b b trapHooks 8472 28
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    have hstep2 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 64#64) s1
        (memRegion (s.sp - 4096#64) 4096 ∗
         ((s.readReg64 .x19 + 560#64) ↦ₛ bs240) ∗
         ((s.readReg64 .x19 + 888#64) ↦₁₂₈ uq888) ∗ ((s.readReg64 .x19 + 904#64) ↦₁₂₈ uq904) ∗
         ((s.readReg64 .x19 + 920#64) ↦₆₄ u920) ∗
         ((s.sp + 240#64) ↦ₛ bs240) ∗
         ((s.sp + 1888#64) ↦₁₂₈ q1888) ∗ ((s.sp + 1904#64) ↦₁₂₈ q1904) ∗
         ((s.sp + 1920#64) ↦₆₄ w1920) ∗ Frame)
        (fun sm Pm =>
          VmPreserved s1 sm ∧
          (Pm ⊢
            memRegion (s.sp - 4096#64) 4096 ∗
            ((s.readReg64 .x19 + 560#64) ↦ₛ bs240) ∗
            ((s.readReg64 .x19 + 888#64) ↦₁₂₈ q1888) ∗ ((s.readReg64 .x19 + 904#64) ↦₁₂₈ q1904) ∗
            ((s.readReg64 .x19 + 920#64) ↦₆₄ w1920) ∗
            ((s.sp + 240#64) ↦ₛ bs240) ∗
            ((s.sp + 1888#64) ↦₁₂₈ q1888) ∗ ((s.sp + 1904#64) ↦₁₂₈ q1904) ∗
            ((s.sp + 1920#64) ↦₆₄ w1920) ∗ Frame) ∧
          sm.sp = s.sp ∧
          TraceCalleeSaved sm s1) := by
      by_vm_steps {
        wp_simp_pre [pointsTo128, sepConj_assoc]
        wp_steps
        simp only [pointsTo128, sepConj_assoc]
        wp_done
      }
    exact SepWP.mono hstep2 fun sm _Pm _ _ ⟨hvm2, hent2, hspm, htr2⟩ =>
      ⟨hent2, hvm1.trans hvm2, hspm, ⟨htr2.1.trans htr1.1, htr2.2.trans htr1.2⟩⟩

/-! ## 3. Shared Error Epilogues (`+60`, `+2044`, `+2048`) -/

/-- Budget-threaded shared `Err(err)` epilogue from `+60` (`+60 -> s0.x30`). -/
theorem states_from_pb_epilogue_60
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : CryptoVerification.LibsignalSpqrV1.Error)
    (v0 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx8_1 : s1.readReg64 .x8 = noneCap)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
        AllocCallPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs1⟩
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 64#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗ Rest))
    (Q := fun sm => AllocCallPreserved s1 sm ∧ sm.sp = s0.sp - 2400#64 ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range_b b trapHooks 60 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [wp_norm, arm64_norm, *]⟩
      dsimp only [resultChunkedStatesAt, noneCap]
      exact Entails.of_eq (by sep_ac_rfl)
    }
  · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, htr2⟩
    have hep := states_from_pb_epilogue_64 s0 s2
      (resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗ Rest)
      hsp0_align hpc2 hrun2 hsp2 htr2
    exact SepWP.mono hep fun sf _Pf _ _ ⟨hPf, hvm_f, hacp_f, hsp_f, hcc_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
       hvm2.trans hvm_f, hacp2.trans hacp_f, hsp_f, hcc_f, htr_f⟩

/-- Budget-threaded shared `Err(err)` exit at `+2048` (`+2048 -> s0.x30`). -/
theorem states_from_pb_err_2048
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : CryptoVerification.LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2048#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx9_1 : (s1.readReg64 .x9).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
        AllocCallPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs1⟩
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte err) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      AllocCallPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range_b b trapHooks 2048 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
      refine ⟨by simp [wp_norm, arm64_norm], ?_, by simp [wp_norm, arm64_norm, noneCap, *]⟩
      have htail := out_8_32_entails_err_tail out (s1.readReg64 .x9)
        18446744073709551615#64 (s1.readReg64 .x13)
      rw [hx9_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x9) ∗
           ((out + 16#64) ↦₆₄ 18446744073709551615#64) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x13) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by sep_ac_rfl))
    }
  · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx8_2, hx19_2, htr2⟩
    exact SepWP.mono
      (states_from_pb_epilogue_60 s0 s2 out err v0 Rest hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2)
      fun sf _Pf _ _ ⟨hPf, hvm_f, hacp_f, hsp_f, hcc_f, htr_f⟩ =>
        ⟨hPf, hvm2.trans hvm_f, hacp2.trans hacp_f, hsp_f, hcc_f, htr_f⟩

/-- Budget-threaded shared `Err(Error::StateDecode)` exit at `+2044` (`+2044 -> s0.x30`). -/
theorem states_from_pb_err_2044
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2044#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
        AllocCallPreserved s1 sf ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rcases htr1 with ⟨htr1, hvregs1⟩
  refine seq_vm_clean (P := libsignalSessionCode) (b := b) (Hk := Rust.withPanics ext)
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2048#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      Rest)
    (Q := fun sm =>
      AllocCallPreserved s1 sm ∧
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x9).extractLsb' 0 8 = spqrErrorByte .stateDecode ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range_b b trapHooks 2044 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    rw [fnAddr_rebase_hooks_eq libsignalSessionCode b trapHooks (Rust.withPanics ext)] at *
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    by_vm_steps {
      wp_steps
      wp_done
    }
  · intro s2 hpc2 hrun2 hvm2 ⟨hacp2, hsp2, hx19_2, hx9_2, htr2⟩
    exact SepWP.mono
      (states_from_pb_err_2048 s0 s2 out .stateDecode Rest
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx9_2 htr2)
      fun sf _Pf _ _ ⟨hPf, hvm_f, hacp_f, hsp_f, hcc_f, htr_f⟩ =>
        ⟨hPf, hvm2.trans hvm_f, hacp2.trans hacp_f, hsp_f, hcc_f, htr_f⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueBudget
