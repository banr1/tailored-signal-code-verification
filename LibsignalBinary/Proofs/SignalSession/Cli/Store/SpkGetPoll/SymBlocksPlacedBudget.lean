/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymBlocksPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Basic-Block Proofs for `get_signed_pre_key::{closure#0}`

Budget-threaded `Vec` deallocation and post-call branch basic-block theorems on Block `571`
(`lsProg_571 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymBlocksPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_571 blkPl_571 lsProg_571)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speWord)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (keyName)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
  (cmn1_add_zero cmn1_beq_zero sepWP_entails_step vecU8Buf_zero_elim words11At words6At)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (deallocBufCellsSpec dropSpeWordCellsSpec optDeallocBufEvents)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] words6At words11At

/-! ## 1. Shared `Vec` deallocation basic blocks -/

theorem freeBytes_180_to_200_placed [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    {st : M.σ} {s : State} {fsp bCap bPtr : BitVec 64} {bBytes : List (BitVec 8)}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_571).base + bv% 180)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = fsp)
    (hx23 : s.readReg64 .x23 = bCap)
    (hx24 : s.readReg64 .x24 = bPtr) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 200) s
      (vecU8Buf A.repAlloc bCap bPtr bBytes ∗ stackAt fsp calleeStk ∗ A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = fsp ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace) ∧
        (Pm ⊢ stackAt fsp calleeStk ∗
          A.pool lim (M.stepEvents (optDeallocBufEvents bCap) st) sm)) := by
  by_cases hbCap : bCap = 0#64
  · rw [hbCap] at hx23 ⊢
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    apply sepWP_entails_step (vecU8Buf_zero_elim A.repAlloc bPtr bBytes)
    rw [emp_sepConj]
    wp_steps_sync_pool ((blkPl_571).base + bv% 200)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_, by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm]
  · have hbCap_beq : (bCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbCap
    simp only [optDeallocBufEvents, hbCap, ↓reduceIte]
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A lim calleeStk) hcrl_d
      ((bCap, bPtr, bBytes, fsp), st)
    clear hcrl hcrl_d hcrl_sf
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hsp' : sf.sp = fsp := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    refine ⟨hsp_align', ⟨hsp', ?_, by simp only [wp_norm, arm64_norm, *]⟩, ?_⟩
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm, *]
    · sep_frame

theorem freeName_200_to_220_placed [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    {st : M.σ} {s0 s : State} {nCap nPtr : BitVec 64} {id : BitVec 32}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_571).base + bv% 200)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx22 : s.readReg64 .x22 = nPtr) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 220) s
      (vecU8Buf A.repAlloc nCap nPtr (keyName id) ∗
        ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗ A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧ CalleeSavedPreserved s sm ∧ sm.trace = s.trace) ∧
        (Pm ⊢ ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗
          A.pool lim (M.stepEvents (optDeallocBufEvents nCap) st) sm)) := by
  by_cases hnCap : nCap = 0#64
  · rw [hnCap]
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    apply sepWP_entails_step (vecU8Buf_zero_elim A.repAlloc nPtr (keyName id))
    rw [emp_sepConj]
    wp_steps_sync_pool ((blkPl_571).base + bv% 220)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_, by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm]
  · have hnCap_beq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    simp only [optDeallocBufEvents, hnCap, ↓reduceIte]
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A lim calleeStk) hcrl_d
      ((nCap, nPtr, keyName id, s0.sp - 384#64), st)
    clear hcrl hcrl_d hcrl_sf
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    refine ⟨hsp_align', ⟨hsp', ?_, by simp only [wp_norm, arm64_norm, *]⟩, ?_⟩
    · rw [CalleeSavedPreserved.iff_regs]
      simp only [wp_norm, arm64_norm, *]
    · sep_frame

theorem freeName_280_to_344_placed [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    {st : M.σ} {s0 s : State} {nCap nPtr : BitVec 64} {id : BitVec 32}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_571).base + bv% 280)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx22 : s.readReg64 .x22 = nPtr) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 344) s
      (vecU8Buf A.repAlloc nCap nPtr (keyName id) ∗
        ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗ A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64 ∧
          sm.readReg64 .x25 = s.readReg64 .x25 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x21 = s.readReg64 .x21) ∧
        (Pm ⊢ ((s0.sp - 248#64) ↦₆₄ nCap) ∗ stackAt (s0.sp - 384#64) calleeStk ∗
          A.pool lim (M.stepEvents (optDeallocBufEvents nCap) st) sm)) := by
  by_cases hnCap : nCap = 0#64
  · rw [hnCap]
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    apply sepWP_entails_step (vecU8Buf_zero_elim A.repAlloc nPtr (keyName id))
    rw [emp_sepConj]
    wp_steps_sync_pool ((blkPl_571).base + bv% 344)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_,
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
    · simp only [wp_norm, arm64_norm]
  · have hnCap_beq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    simp only [optDeallocBufEvents, hnCap, ↓reduceIte]
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A lim calleeStk) hcrl_d
      ((nCap, nPtr, keyName id, s0.sp - 384#64), st)
    clear hcrl hcrl_d hcrl_sf
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    wp_steps_sync_pool ((blkPl_571).base + bv% 344)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simpa only [wp_norm, arm64_norm] using hsp_align',
      ⟨by simpa only [wp_norm, arm64_norm] using hsp',
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *]⟩,
      by sep_frame⟩

/-! ## 2. Post-`Dir::get` / post-`decode_kyber_pre_key` deallocating branch blocks -/

theorem step_missing_88_to_200_placed [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    {st : M.σ} {s0 s : State} {g0 g1 g2 g3 c3 c4 b2 b3 d3 d4 : BitVec 64}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hg0 : g0 = okTagVec)
    (hg3 : g3 = 0#64)
    (hpc : s.pc = (blkPl_571).base + bv% 88)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 200) s
      (vecU8Buf A.repAlloc g1 g2 [] ∗
        ((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
        ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3) ∗
        ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
        ((s0.sp - 320#64) ↦₆₄ b2) ∗ ((s0.sp - 312#64) ↦₆₄ b3) ∗
        ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4) ∗
        stackAt (s0.sp - 384#64) calleeStk ∗ A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x28 = s.readReg64 .x28 ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧
          sm.readReg64 .x26 = 0xFFFFFFFFFFFFFFFF#64) ∧
        (Pm ⊢ ((s0.sp - 200#64) ↦₆₄ g0) ∗ ((s0.sp - 192#64) ↦₆₄ g1) ∗
          ((s0.sp - 184#64) ↦₆₄ g2) ∗ ((s0.sp - 176#64) ↦₆₄ g3) ∗
          ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
          ((s0.sp - 320#64) ↦₆₄ c3) ∗ ((s0.sp - 312#64) ↦₆₄ c4) ∗
          ((s0.sp - 224#64) ↦₆₄ c3) ∗ ((s0.sp - 216#64) ↦₆₄ c4) ∗
          stackAt (s0.sp - 384#64) calleeStk ∗
          A.pool lim (M.stepEvents (optDeallocBufEvents g1) st) sm)) := by
  subst hg0; subst hg3
  dsimp only [okTagVec]
  by_cases hg1 : g1 = 0#64
  · rw [hg1]
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    apply sepWP_entails_step (vecU8Buf_zero_elim A.repAlloc g2 [])
    rw [emp_sepConj]
    wp_steps_sync_pool ((blkPl_571).base + bv% 200)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_,
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simp only [wp_norm, arm64_norm],
      by simpa only [wp_norm, arm64_norm] using hx29,
      by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
    · simpa only [wp_norm, arm64_norm] using hsp_align
    · simpa only [wp_norm, arm64_norm] using hsp
    · simp only [wp_norm, arm64_norm]
  · have hg1_beq : (g1 == 0#64) = false := beq_eq_false_iff_ne.mpr hg1
    simp only [optDeallocBufEvents, hg1, ↓reduceIte]
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A lim calleeStk) hcrl_d
      ((g1, g2, [], s0.sp - 384#64), st)
    clear hcrl hcrl_d hcrl_sf
    try
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    refine ⟨hsp_align',
      ⟨hsp',
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *]⟩,
      by sep_frame⟩

theorem step_decodeErr_124_to_280_placed [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    {st : M.σ} {s0 s : State} {g1 g2 w0 w1 w2 w3 w4 w5 w6 b0 b1 b2 b3 c3 c4 : BitVec 64}
    {b : BitVec 8} {bs : List (BitVec 8)}
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hw0 : w0 = 0xFFFFFFFFFFFFFFFF#64)
    (hpc : s.pc = (blkPl_571).base + bv% 124)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx23 : s.readReg64 .x23 = g1)
    (hx24 : s.readReg64 .x24 = g2)
    (hx27 : s.readReg64 .x27 = s0.sp - 200#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 280) s
      (vecU8Buf A.repAlloc g1 g2 (b :: bs) ∗
        ((s0.sp - 200#64) ↦₆₄ w0) ∗ ((s0.sp - 192#64) ↦₆₄ w1) ∗
        ((s0.sp - 184#64) ↦₆₄ w2) ∗ ((s0.sp - 176#64) ↦₆₄ w3) ∗
        ((s0.sp - 168#64) ↦₆₄ w4) ∗ ((s0.sp - 160#64) ↦₆₄ w5) ∗
        ((s0.sp - 152#64) ↦₆₄ w6) ∗
        ((s0.sp - 336#64) ↦₆₄ b0) ∗ ((s0.sp - 328#64) ↦₆₄ b1) ∗
        ((s0.sp - 320#64) ↦₆₄ b2) ∗ ((s0.sp - 312#64) ↦₆₄ b3) ∗
        ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4) ∗
        stackAt (s0.sp - 384#64) calleeStk ∗ A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x25 = w1 ∧
          sm.readReg64 .x23 = w2 ∧
          sm.readReg64 .x24 = w3 ∧
          sm.readReg64 .x21 = w4) ∧
        (Pm ⊢ ((s0.sp - 200#64) ↦₆₄ w0) ∗ ((s0.sp - 192#64) ↦₆₄ w1) ∗
          ((s0.sp - 184#64) ↦₆₄ w2) ∗ ((s0.sp - 176#64) ↦₆₄ w3) ∗
          ((s0.sp - 168#64) ↦₆₄ w4) ∗ ((s0.sp - 160#64) ↦₆₄ w5) ∗
          ((s0.sp - 152#64) ↦₆₄ w6) ∗
          ((s0.sp - 336#64) ↦₆₄ w5) ∗ ((s0.sp - 328#64) ↦₆₄ w6) ∗
          ((s0.sp - 320#64) ↦₆₄ w5) ∗ ((s0.sp - 312#64) ↦₆₄ w6) ∗
          ((s0.sp - 272#64) ↦₆₄ w5) ∗ ((s0.sp - 264#64) ↦₆₄ w6) ∗
          stackAt (s0.sp - 384#64) calleeStk ∗
          A.pool lim (M.stepEvents (optDeallocBufEvents g1) st) sm)) := by
  subst hw0
  by_cases hg1 : g1 = 0#64
  · rw [hg1] at hx23 ⊢
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    apply sepWP_entails_step (vecU8Buf_zero_elim A.repAlloc g2 (b :: bs))
    rw [emp_sepConj]
    wp_steps_sync_pool ((blkPl_571).base + bv% 280)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ⟨?_, ?_,
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
    · simp only [wp_norm, arm64_norm]
  · have hg1_beq : (g1 == 0#64) = false := beq_eq_false_iff_ne.mpr hg1
    simp only [optDeallocBufEvents, hg1, ↓reduceIte]
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    wp_call_spec_lscro hDeallocCells (deallocBufCellsSpec A lim calleeStk) hcrl_d
      ((g1, g2, b :: bs, s0.sp - 384#64), st)
    clear hcrl hcrl_d hcrl_sf
    have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
    have hsp_align' : sf.spAligned = true := by
      simp only [State.spAligned, hsp'] at hsp_align ⊢
      simpa only [hsp] using hsp_align
    wp_steps_sync_pool ((blkPl_571).base + bv% 280)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simpa only [wp_norm, arm64_norm] using hsp_align',
      ⟨by simpa only [wp_norm, arm64_norm] using hsp',
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *]⟩,
      by sep_frame⟩

theorem step_found_220_to_344_placed [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    {st : M.σ} {s0 s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64}
    {a1 a2 a3 a4 b0 b1 : BitVec 64}
    (hDropCells : subroutine_ok (lsProg_571 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec A lim calleeStk)))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hw0 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hpc : s.pc = (blkPl_571).base + bv% 220)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : s.readReg64 .x26 = w0)
    (hx25 : s.readReg64 .x25 = w1)
    (hx28 : s.readReg64 .x28 = w2)
    (hx21 : s.readReg64 .x21 = w4) :
    SepWP (lsProg_571 H) ((blkPl_571).base + bv% 344) s
      (words6At (s0.sp - 200#64) w0 w1 w2 w3 w4 w5 ∗
        ((s0.sp - 376#64) ↦₆₄ w3) ∗ ((s0.sp - 368#64) ↦₆₄ a1) ∗ ((s0.sp - 360#64) ↦₆₄ a2) ∗
        ((s0.sp - 352#64) ↦₆₄ a3) ∗ ((s0.sp - 344#64) ↦₆₄ a4) ∗
        ((s0.sp - 336#64) ↦₆₄ b0) ∗ ((s0.sp - 328#64) ↦₆₄ b1) ∗
        ((s0.sp - 304#64) ↦₆₄ w7) ∗ ((s0.sp - 296#64) ↦₆₄ w8) ∗
        ((s0.sp - 288#64) ↦₆₄ w9) ∗ ((s0.sp - 280#64) ↦₆₄ w10) ∗
        ((s0.sp - 224#64) ↦₆₄ w5) ∗ ((s0.sp - 216#64) ↦₆₄ w6) ∗
        stackAt (s0.sp - 384#64) calleeStk ∗ A.pool lim st s)
      (fun sm Pm =>
        sm.spAligned = true ∧
        (sm.sp = s0.sp - 384#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s ∧
          sm.trace = s.trace ∧
          sm.readReg64 .x19 = s.readReg64 .x19 ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x26 = w0 ∧
          sm.readReg64 .x25 = w1 ∧
          sm.readReg64 .x23 = w2 ∧
          sm.readReg64 .x24 = w3 ∧
          sm.readReg64 .x21 = w4) ∧
        (Pm ⊢ (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64,
            ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ e5 : BitVec 64,
              words6At (s0.sp - 200#64) e0 e1 e2 e3 e4 e5) ∗
          ((s0.sp - 376#64) ↦₆₄ w3) ∗ ((s0.sp - 368#64) ↦₆₄ w7) ∗ ((s0.sp - 360#64) ↦₆₄ w8) ∗
          ((s0.sp - 352#64) ↦₆₄ w9) ∗ ((s0.sp - 344#64) ↦₆₄ w10) ∗
          ((s0.sp - 336#64) ↦₆₄ w5) ∗ ((s0.sp - 328#64) ↦₆₄ w6) ∗
          ((s0.sp - 304#64) ↦₆₄ w7) ∗ ((s0.sp - 296#64) ↦₆₄ w8) ∗
          ((s0.sp - 288#64) ↦₆₄ w9) ∗ ((s0.sp - 280#64) ↦₆₄ w10) ∗
          ((s0.sp - 224#64) ↦₆₄ w5) ∗ ((s0.sp - 216#64) ↦₆₄ w6) ∗
          stackAt (s0.sp - 384#64) calleeStk ∗ A.pool lim st sm)) := by
  have _hcmn1 := cmn1_beq_zero hw0
  have _hcmn2 := cmn1_add_zero hw0
  dsimp only [words6At, speWord]
  apply sepWP_seq_lscro (mid := lsmpl.base 553) hcrl
  wp_steps_sync_pool (lsmpl.base 553)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_d
  wp_call_spec_lscro hDropCells (dropSpeWordCellsSpec A lim calleeStk) hcrl_d
    ((s0.sp - 200#64, w1, w2, w3, w4, w5, s0.sp - 384#64), st)
  clear hcrl hcrl_d hcrl_sf
  have hsp' : sf.sp = s0.sp - 384#64 := by simpa only [wp_norm, arm64_norm, hsp] using hsp_sf
  have hsp_align' : sf.spAligned = true := by
    simp only [State.spAligned, hsp'] at hsp_align ⊢
    simpa only [hsp] using hsp_align
  wp_steps_sync_pool ((blkPl_571).base + bv% 344)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨by simpa only [wp_norm, arm64_norm] using hsp_align',
    ⟨by simpa only [wp_norm, arm64_norm] using hsp',
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm, *]⟩,
    by sep_frame⟩

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymBlocksPlacedBudget
