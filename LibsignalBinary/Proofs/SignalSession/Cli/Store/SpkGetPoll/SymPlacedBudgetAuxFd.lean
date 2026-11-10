/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymBlocksPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Basic-Block Steppers and Combinators for `get_signed_pre_key::{closure#0}`

Pure basic-block steppers transporting `A.pool` and `fs`, plus symbolic-execution cut combinators
for Block `571` (`lsProg_571 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlacedBudgetAuxFd

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speWord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli
  (DirGhost PkPollGhost ReadRule keyName)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_571 blkPC_571 blkPl_571 lsProg_571)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (SepWPp.call_lscro)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
  (cmn1_add_zero cmn1_beq_zero len_bv_ne_zero sepWP_frame_right
   sp200_16 sp200_24 sp200_32 sp200_40 sp200_48 sp200_56 sp200_64 sp200_72 sp200_8 sp200_80
   sp248_16 sp248_8 spkSavedAt words11At words6At)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers.CliSpkPollNorm
  (bv_sub_sub_lit extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre
   readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre
   readReg_setPC_pre readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudgetFd
  (spkPanicQp_fd spkPostQ_fd)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi bv_sub_sub_lit
attribute [local arm64_norm, local wp_norm] words6At words11At

/-! ## 1. Pure Basic-Block Steppers with `A.pool` & `fs` Transport (`lsProg_571 H`) -/

theorem step_entry_to_decimal_pool_placed_fd [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {x : PkPollGhost} {s0 : State}
    {r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : BitVec 64}
    (hpc : s0.pc = (blkPl_571).base)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.fut)
    (hx8 : s0.readReg64 .x8 = x.out) :
    SepWP (lsProg_571 H) (lsmpl.base 597) s0
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        ((s0.sp - 96#64) ↦₆₄ r0) ∗ ((s0.sp - 88#64) ↦₆₄ r1) ∗
        ((s0.sp - 80#64) ↦₆₄ r2) ∗ ((s0.sp - 72#64) ↦₆₄ r3) ∗
        ((s0.sp - 64#64) ↦₆₄ r4) ∗ ((s0.sp - 56#64) ↦₆₄ r5) ∗
        ((s0.sp - 48#64) ↦₆₄ r6) ∗ ((s0.sp - 40#64) ↦₆₄ r7) ∗
        ((s0.sp - 32#64) ↦₆₄ r8) ∗ ((s0.sp - 24#64) ↦₆₄ r9) ∗
        ((s0.sp - 16#64) ↦₆₄ r10) ∗ ((s0.sp - 8#64) ↦₆₄ r11) ∗
        A.pool lim st s0)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.fs = s0.fs ∧
          sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.trace = s0.trace ∧
          sm.fs.files = s0.fs.files ∧
          sm.readReg64 .x0 = s0.sp - 248#64 ∧
          sm.readReg32 .x1 = x.id ∧
          sm.readReg64 .x30 = (blkPl_571).base + bv% 68 ∧
          sm.readReg64 .x19 = x.fut ∧
          sm.readReg64 .x20 = x.out ∧
          sm.readReg64 .x21 = x.self ∧
          sm.readReg64 .x27 = s0.sp - 200#64 ∧
          sm.readReg64 .x29 = s0.sp - 96#64) ∧
        (Pm ⊢ (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
          spkSavedAt s0 ∗ A.pool lim st sm)) := by
  dsimp only [spkSavedAt]
  wp_steps_sync_pool (lsmpl.base 597)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
  · simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢
    bv_omega

theorem step_68_to_dirGet_pool_placed_fd [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {x : PkPollGhost} {s0 s : State} {nPtr : BitVec 64}
    (hpc : s.pc = (blkPl_571).base + bv% 68)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) (lsmpl.base 589) s
      (((s0.sp - 240#64) ↦₆₄ nPtr) ∗
        ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
        A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.fs = s.fs ∧
          sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.fs.files = s.fs.files ∧
          sm.readReg64 .x0 = s0.sp - 200#64 ∧
          sm.readReg64 .x1 = x.self ∧
          sm.readReg64 .x2 = nPtr ∧
          sm.readReg64 .x3 = BitVec.ofNat 64 (keyName x.id).length ∧
          sm.readReg64 .x30 = (blkPl_571).base + bv% 88 ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = nPtr ∧
          sm.readReg64 .x27 = s.readReg64 .x27 ∧
          sm.readReg64 .x29 = s0.sp - 96#64) ∧
        (Pm ⊢ ((s0.sp - 240#64) ↦₆₄ nPtr) ∗
          ((s0.sp - 232#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          A.pool lim st sm)) := by
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨by simp only [wp_norm, arm64_norm], ?_,
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simpa only [wp_norm, arm64_norm] using hx29⟩, by sep_frame⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp

theorem step_88_to_decodeSpk_pool_placed_fd [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {g0 g1 g2 g3 : BitVec 64} {b : BitVec 8} {bs : List (BitVec 8)}
    (hg0 : g0 = okTagVec)
    (hg3 : g3 = BitVec.ofNat 64 (b :: bs).length)
    (hlen_lt : (b :: bs).length < 2 ^ 32)
    (hpc : s.pc = (blkPl_571).base + bv% 88)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) (lsmpl.base 595) s
      (((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
        ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3) ∗
        A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.fs = s.fs ∧
          sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x0 = s0.sp - 200#64 ∧
          sm.readReg64 .x1 = g2 ∧
          sm.readReg64 .x2 = BitVec.ofNat 64 (b :: bs).length ∧
          sm.readReg64 .x30 = (blkPl_571).base + bv% 124 ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = g1 ∧
          sm.readReg64 .x24 = g2 ∧
          sm.readReg64 .x27 = s.readReg64 .x27 ∧
          sm.readReg64 .x29 = s0.sp - 96#64) ∧
        (Pm ⊢ ((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
          ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3) ∗
          A.pool lim st sm)) := by
  subst hg0; subst hg3
  have _hlen_beq : (BitVec.ofNat 64 (b :: bs).length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (len_bv_ne_zero hlen_lt)
  dsimp only [okTagVec]
  wp_steps_sync_pool (lsmpl.base 595)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨by simp only [wp_norm, arm64_norm], ?_,
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simpa only [wp_norm, arm64_norm] using hx29⟩, by sep_frame⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp

theorem step_readErr_88_to_280_pool_placed_fd [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {g0 g1 g2 g3 g4 g5 b0 b1 : BitVec 64}
    (hg0 : g0 = speWord 1)
    (hpc : s.pc = (blkPl_571).base + bv% 88)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 200#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 280) s
      (words6At (s0.sp - 200#64) g0 g1 g2 g3 g4 g5 ∗
        ((s0.sp - 336#64) ↦₆₄ b0) ∗ ((s0.sp - 328#64) ↦₆₄ b1) ∗
        A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.fs = s.fs ∧
          sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x25 = g0 ∧
          sm.readReg64 .x23 = g1 ∧
          sm.readReg64 .x24 = g2 ∧
          sm.readReg64 .x21 = g3) ∧
        (Pm ⊢ words6At (s0.sp - 200#64) g0 g1 g2 g3 g4 g5 ∗
          ((s0.sp - 336#64) ↦₆₄ g4) ∗ ((s0.sp - 328#64) ↦₆₄ g5) ∗
          A.pool lim st sm)) := by
  subst hg0
  dsimp only [words6At, speWord]
  wp_steps_sync_pool ((blkPl_571).base + bv% 280)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨by simp only [wp_norm, arm64_norm], ?_,
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp

theorem step_missing_220_to_344_pool_placed_fd [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State} {e0 : BitVec 64}
    (hpc : s.pc = (blkPl_571).base + bv% 220)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : s.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 344) s
      (((s0.sp - 200#64) ↦₆₄ e0) ∗ A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.fs = s.fs ∧
          sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64 ∧
          sm.readReg64 .x25 = speWord 14 ∧
          sm.readReg64 .x23 = s.readReg64 .x28 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x21 = s.readReg64 .x21) ∧
        (Pm ⊢ ((s0.sp - 200#64) ↦₆₄ speWord 14) ∗ A.pool lim st sm)) := by
  dsimp only [speWord]
  wp_steps_sync_pool ((blkPl_571).base + bv% 344)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨by simp only [wp_norm, arm64_norm], ?_,
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simpa only [wp_norm, arm64_norm] using hx26,
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp

theorem step_found_124_to_180_pool_placed_fd [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {s0 s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64}
    {a0 b2 b3 b4 c0 c1 c2 c3 c4 d3 d4 : BitVec 64}
    (hw0 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hpc : s.pc = (blkPl_571).base + bv% 124)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 200#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 180) s
      (words11At (s0.sp - 200#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
        ((s0.sp - 376#64) ↦₆₄ a0) ∗
        ((s0.sp - 320#64) ↦₆₄ b2) ∗ ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4) ∗
        ((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
        ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
        ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4) ∗
        A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.fs = s.fs ∧
          sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x26 = w0 ∧
          sm.readReg64 .x25 = w1 ∧
          sm.readReg64 .x28 = w2 ∧
          sm.readReg64 .x21 = w4) ∧
        (Pm ⊢ words11At (s0.sp - 200#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          ((s0.sp - 376#64) ↦₆₄ w3) ∗
          ((s0.sp - 320#64) ↦₆₄ w5) ∗ ((s0.sp - 312#64) ↦₆₄ w6) ∗ ((s0.sp - 304#64) ↦₆₄ w7) ∗
          ((s0.sp - 296#64) ↦₆₄ w8) ∗ ((s0.sp - 288#64) ↦₆₄ w9) ∗ ((s0.sp - 280#64) ↦₆₄ w10) ∗
          ((s0.sp - 272#64) ↦₆₄ w5) ∗ ((s0.sp - 264#64) ↦₆₄ w6) ∗
          ((s0.sp - 224#64) ↦₆₄ w5) ∗ ((s0.sp - 216#64) ↦₆₄ w6) ∗
          A.pool lim st sm)) := by
  have _hcmn1 := cmn1_beq_zero hw0
  have _hcmn2 := cmn1_add_zero hw0
  dsimp only [words11At]
  wp_steps_sync_pool ((blkPl_571).base + bv% 180)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, ⟨by simp only [wp_norm, arm64_norm], ?_,
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simpa only [wp_norm, arm64_norm] using hx29,
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
  · simpa only [wp_norm, arm64_norm] using hsp_align
  · simpa only [wp_norm, arm64_norm] using hsp

/-! ## 2. Top-Level Symbolic Execution Combinators -/

theorem freeOnlyEvs_optDeallocBufEvents_p (cap : BitVec 64) :
    FreeOnlyEvs (optDeallocBufEvents cap) := by
  unfold optDeallocBufEvents
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

theorem entails_pure_pre_p {P Spatial F : SepProp} {φ : Prop}
    (hφ : φ)
    (hS : P ⊢ Spatial ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame) :
    P ⊢ (⌜φ⌝ ∗ Spatial) ∗ F :=
  Entails.trans hS (sepConj_mono_left (Entails.pure_right hφ (Entails.refl _)))

theorem sepWPp_pull_pure_p {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {Body F : SepProp} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (Body ∗ F) post Qp) :
    SepWPp prog ret s ((⌜φ⌝ ∗ Body) ∗ F) post Qp := by
  intro R hm hL
  have heq : ((⌜φ⌝ ∗ Body) ∗ F) ∗ R = ⌜φ⌝ ∗ ((Body ∗ F) ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem sepWPp_pull_pure2_p {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {W Det Tail F : SepProp} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s ((W ∗ (Det ∗ Tail)) ∗ F) post Qp) :
    SepWPp prog ret s ((W ∗ ((⌜φ⌝ ∗ Det) ∗ Tail)) ∗ F) post Qp := by
  intro R hm hL
  have heq : ((W ∗ ((⌜φ⌝ ∗ Det) ∗ Tail)) ∗ F) ∗ R =
      ⌜φ⌝ ∗ (((W ∗ (Det ∗ Tail)) ∗ F) ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem sepWPp_elim_exists_p {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Body : α → SepProp} {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v : α, SepWPp prog ret s (Body v ∗ Rest) post Qp) :
    SepWPp prog ret s ((∃∗ v : α, Body v) ∗ Rest) post Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨v, hm⟩
  exact h v R hm hL

theorem sepWPp_exists_mid_p {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp} {Body : α → SepProp} {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v : α, SepWPp prog ret s (Acc ∗ (Body v ∗ Rest)) post Qp) :
    SepWPp prog ret s (Acc ∗ ((∃∗ v : α, Body v) ∗ Rest)) post Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left,
    satisfies_sepExists] at hm
  rcases hm with ⟨v, hm⟩
  exact h v R hm hL

theorem sepWPp_shift_p {prog : Program} {ret : BitVec 64} {s : State}
    {Acc C Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s ((Acc ∗ C) ∗ Rest) post Qp) :
    SepWPp prog ret s (Acc ∗ (C ∗ Rest)) post Qp := by
  have heq : Acc ∗ (C ∗ Rest) = (Acc ∗ C) ∗ Rest := (sepConj_assoc Acc C Rest).symm
  rw [heq]
  exact h

theorem sepWPp_mid_5_p {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp}
    {B : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 v4 : BitVec 64,
      SepWPp prog ret s (Acc ∗ (B v0 v1 v2 v3 v4 ∗ Rest)) post Qp) :
    SepWPp prog ret s
      (Acc ∗ ((∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, B v0 v1 v2 v3 v4) ∗ Rest)) post Qp :=
  sepWPp_exists_mid_p fun v0 => sepWPp_exists_mid_p fun v1 => sepWPp_exists_mid_p fun v2 =>
    sepWPp_exists_mid_p fun v3 => sepWPp_exists_mid_p fun v4 => h v0 v1 v2 v3 v4

theorem sepWPp_mid_6_p {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp}
    {B : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 v4 v5 : BitVec 64,
      SepWPp prog ret s (Acc ∗ (B v0 v1 v2 v3 v4 v5 ∗ Rest)) post Qp) :
    SepWPp prog ret s
      (Acc ∗ ((∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
          B v0 v1 v2 v3 v4 v5) ∗ Rest)) post Qp :=
  sepWPp_exists_mid_p fun v0 => sepWPp_exists_mid_p fun v1 => sepWPp_exists_mid_p fun v2 =>
    sepWPp_exists_mid_p fun v3 => sepWPp_exists_mid_p fun v4 => sepWPp_exists_mid_p fun v5 =>
    h v0 v1 v2 v3 v4 v5

theorem sepWPp_mid_11_p {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp}
    {B : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp}
    {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : BitVec 64,
      SepWPp prog ret s (Acc ∗ (B v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ∗ Rest)) post Qp) :
    SepWPp prog ret s
      (Acc ∗ ((∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64,
          B v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) ∗ Rest)) post Qp :=
  sepWPp_exists_mid_p fun v0 => sepWPp_exists_mid_p fun v1 => sepWPp_exists_mid_p fun v2 =>
    sepWPp_exists_mid_p fun v3 => sepWPp_exists_mid_p fun v4 => sepWPp_exists_mid_p fun v5 =>
    sepWPp_exists_mid_p fun v6 => sepWPp_exists_mid_p fun v7 => sepWPp_exists_mid_p fun v8 =>
    sepWPp_exists_mid_p fun v9 => sepWPp_exists_mid_p fun v10 =>
    h v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10

theorem sepWP_elim_words6_exists_p {prog : Program} {pc : BitVec 64} {s : State}
    {a : BitVec 64} {Rest F : SepProp} {post : State → SepProp → Prop}
    (h : ∀ e0 e1 e2 e3 e4 e5 : BitVec 64,
      SepWP prog pc s ((words6At a e0 e1 e2 e3 e4 e5 ∗ Rest) ∗ F) post) :
    SepWP prog pc s
      (((∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64,
          words6At a e0 e1 e2 e3 e4 e5) ∗ Rest) ∗ F) post := by
  unfold SepWP reaches_pc at h ⊢
  intro R hm hL
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨e0, e1, e2, e3, e4, e5, hm⟩
  exact h e0 e1 e2 e3 e4 e5 R hm hL

theorem sp_aligned_of_eq_p {s1 s2 : State} (halign : s1.spAligned = true)
    (hsp : s2.sp = s1.sp) : s2.spAligned = true := by
  simp only [State.spAligned, hsp] at halign ⊢
  exact halign

theorem sepWP_frame_cut_pool_placed [LibsignalPlacement] {prog : Program}
    {mid target_pc : BitVec 64} {s : State} {P P_sub F : SepProp} {Q_sub : State → SepProp}
    {post : State → SepProp → Prop} {Φ : State → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P_sub (fun sm Pm => sm.spAligned = true ∧ Φ sm ∧ (Pm ⊢ Q_sub sm)))
    (hP : P ⊢ P_sub ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame)
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → sm.spAligned = true →
      LibsignalCodeRoLoaded lsmpl sm.mem → Φ sm → SepWP prog target_pc sm (Q_sub sm ∗ F) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.weaken_pre hP ?_
  refine sepWP_seq_lscro (mid := mid) hcrl ?_
  exact sepWP_frame_right (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hspm, hΦm, hent⟩ hcrlm =>
    SepWP.weaken_pre (sepConj_mono_left hent) (h2 sm hpcm hrunm hspm hcrlm hΦm))

theorem sepWPp_frame_cut_pool_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_sub F : SepProp} {Q_sub : State → SepProp}
    {post Qp : State → SepProp → Prop} {Φ : State → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P_sub (fun sm Pm => sm.spAligned = true ∧ Φ sm ∧ (Pm ⊢ Q_sub sm)))
    (hP : P ⊢ P_sub ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame)
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → sm.spAligned = true →
      LibsignalCodeRoLoaded lsmpl sm.mem → Φ sm → SepWPp prog ret sm (Q_sub sm ∗ F) post Qp) :
    SepWPp prog ret s P post Qp := by
  refine SepWPp.weaken_pre hP ?_
  refine sepWPp_seq_lscro (mid := mid) hcrl ?_
  exact sepWP_frame_right (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hspm, hΦm, hent⟩ hcrlm =>
    SepWPp.weaken_pre (sepConj_mono_left hent) (h2 sm hpcm hrunm hspm hcrlm hΦm))

theorem sepWPp_call_cells_p_fd [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {calleeStk : Nat} {x0 : PkPollGhost} {st0 : M.σ} {R0 : SepProp}
    {entry ret_pc : BitVec 64} {spec : Spec α} {g : α}
    {s0 s : State} {P F : SepProp}
    (hcall : subroutine_ok (lsProg_571 H) entry
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed spec)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpan_eq : ∀ sf, spec.onPanic g s sf = ⌜False⌝)
    (hexit_eq : ∀ code sf, spec.onExit g code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom g s sf = ⌜False⌝)
    (hP : P ⊢ spec.pre g s ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      FdsGe3Closed sf.fs →
      SepWPp (lsProg_571 H) (s0.readReg64 .x30) sf
        (spec.post g s sf ∗ F)
        (spkPostQ_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0)
        (spkPanicQp_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0)) :
    SepWPp (lsProg_571 H) (s0.readReg64 .x30) s P
      (spkPostQ_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0)
      (spkPanicQp_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0) := by
  refine SepWPp.call_lscro (pl := lsmpl) (spec := withFdsGe3Closed spec) (x := g) (F := F)
    hcall hcrl hpc hrun hsp hlr
    (fun R hm => by
      dsimp only [withFdsGe3Closed]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfds, ?_⟩
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hP) hm)
    (fun sf code R' _ hex => by
      dsimp only [withFdsGe3Closed] at hex
      rw [hexit_eq] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ hm => by
      dsimp only [withFdsGe3Closed] at hm
      rw [hpan_eq, sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcrl_sf => by
      dsimp only [withFdsGe3Closed]
      exact sepWPp_pull_pure_p (hnext sf hpc_sf hrun_sf hsp_sf hcs_sf hcrl_sf))
    (h_no_oom := fun R' sf _ ho => by
      dsimp only [withFdsGe3Closed] at ho
      rw [hoom_eq] at ho
      exact (not_satisfies_false_sepConj ho).elim)

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlacedBudgetAuxFd
