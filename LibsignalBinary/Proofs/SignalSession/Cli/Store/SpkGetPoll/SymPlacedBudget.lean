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
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymBlocksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Symbolic Execution of `get_signed_pre_key::{closure#0}`

Proves budget-threaded `spkGetPollInner_placed_ok` and `spkGetPoll_placed_fs_ok` on Block `571`
(`lsProg_571 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speWord)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded TraceFsSound extract_withLsCodeRoLoaded sepWP_seq_lscro
   sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (SignedPreKeyRecord)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost PkAns PkPollGhost ReadRule dirAt keyName pkAnsOf pkBoxAt spkAnsAt)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_571 blkPC_571 blkPl_571 lsProg_571)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (SepWPp.call_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
  (cells_48_split cells_sub_5_152_eq cells_sub_5_248_eq cells_sub_5_296_eq cells_sub_5_336_eq
   cells_sub_5_376_eq cells_sub_6_200_eq cells_sub_6_48_eq cells_sub_6_96_eq cmn1_add_zero
   cmn1_beq_zero csp_regs decodeErr88_pack_cells decodeSpkDetached dirGetDetached
   found88_pack_cells len_bv_ne_zero memRegion_88_cells memRegion_bound_of_pointsTo64
   missing88_pack_cells readErr88_pack_cells sepWP_frame_right
   sp200_16 sp200_24 sp200_32 sp200_40 sp200_48 sp200_56 sp200_64 sp200_72 sp200_8 sp200_80
   sp248_16 sp248_8 spkPollSlack spkSavedAt spkScratch15 stackAt_spkPoll_frame
   stackAt_sub_split words11At words6At)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers.CliSpkPollNorm
  (bv_sub_sub_lit extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre
   readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre
   readReg_setPC_pre readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkLoopEnv decodeSignedPreKeyPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced decimalSpecPlaced dirGetSpecPlaced dropSpeWordSpecPlaced
   pkGetPollSpecOfPlaced spkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (CliSpkGetPollEnv OptSpkDecodeEnv decimalCellsSpec decodeSpkCellsSpec dirGetCellsSpec
   optDeallocBufEvents spkGetPollInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudget
  (spkEpiPre spkPanicQp spkPostQ)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudget
  (deallocBuf_cells_placed_ok decimal_cells_placed_ok decodeSpk_cells_placed_ok
   dirGet_cells_placed_ok dropSpeWord_cells_placed_ok epilogue_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymBlocksPlacedBudget
  (freeBytes_180_to_200_placed freeName_200_to_220_placed freeName_280_to_344_placed
   step_decodeErr_124_to_280_placed step_found_220_to_344_placed step_missing_88_to_200_placed)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi bv_sub_sub_lit
attribute [local arm64_norm, local wp_norm] words6At words11At

/-! ## 1. Pure Basic-Block Steppers with `A.pool` Transport (`lsProg_571 H`) -/

private theorem step_entry_to_decimal_pool_placed [LibsignalPlacement] {H : LibsignalHooks}
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
        (sm.sp = s0.sp - 384#64 ∧
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
    by simp only [wp_norm, arm64_norm]⟩, by sep_frame⟩
  · simp only [State.spAligned, wp_norm, arm64_norm] at hsp_align ⊢
    bv_omega

private theorem step_68_to_dirGet_pool_placed [LibsignalPlacement] {H : LibsignalHooks}
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
        (sm.sp = s0.sp - 384#64 ∧
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
  refine ⟨?_, ⟨?_,
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

private theorem step_88_to_decodeSpk_pool_placed [LibsignalPlacement] {H : LibsignalHooks}
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
        (sm.sp = s0.sp - 384#64 ∧
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
  refine ⟨?_, ⟨?_,
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

private theorem step_readErr_88_to_280_pool_placed [LibsignalPlacement] {H : LibsignalHooks}
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
        (sm.sp = s0.sp - 384#64 ∧
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
  refine ⟨?_, ⟨?_,
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

private theorem step_missing_220_to_344_pool_placed [LibsignalPlacement] {H : LibsignalHooks}
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
        (sm.sp = s0.sp - 384#64 ∧
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
  refine ⟨?_, ⟨?_,
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

private theorem step_found_124_to_180_pool_placed [LibsignalPlacement] {H : LibsignalHooks}
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
        (sm.sp = s0.sp - 384#64 ∧
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
  refine ⟨?_, ⟨?_,
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

private theorem freeOnlyEvs_optDeallocBufEvents_p (cap : BitVec 64) :
    FreeOnlyEvs (optDeallocBufEvents cap) := by
  unfold optDeallocBufEvents
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

private theorem entails_pure_pre_p {P Spatial F : SepProp} {φ : Prop}
    (hφ : φ)
    (hS : P ⊢ Spatial ∗ F := by
      try simp only [words11At, words6At, spkSavedAt,
        sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
        sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
      sep_frame) :
    P ⊢ (⌜φ⌝ ∗ Spatial) ∗ F :=
  Entails.trans hS (sepConj_mono_left (Entails.pure_right hφ (Entails.refl _)))

private theorem sepWPp_pull_pure_p {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {Body F : SepProp} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (Body ∗ F) post Qp) :
    SepWPp prog ret s ((⌜φ⌝ ∗ Body) ∗ F) post Qp := by
  intro R hm hL
  have heq : ((⌜φ⌝ ∗ Body) ∗ F) ∗ R = ⌜φ⌝ ∗ ((Body ∗ F) ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem sepWPp_pull_pure2_p {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {W Det Tail F : SepProp} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s ((W ∗ (Det ∗ Tail)) ∗ F) post Qp) :
    SepWPp prog ret s ((W ∗ ((⌜φ⌝ ∗ Det) ∗ Tail)) ∗ F) post Qp := by
  intro R hm hL
  have heq : ((W ∗ ((⌜φ⌝ ∗ Det) ∗ Tail)) ∗ F) ∗ R =
      ⌜φ⌝ ∗ (((W ∗ (Det ∗ Tail)) ∗ F) ∗ R) := by sep_ac_rfl
  rw [heq, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

private theorem sepWPp_elim_exists_p {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Body : α → SepProp} {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v : α, SepWPp prog ret s (Body v ∗ Rest) post Qp) :
    SepWPp prog ret s ((∃∗ v : α, Body v) ∗ Rest) post Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨v, hm⟩
  exact h v R hm hL

private theorem sepWPp_exists_mid_p {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {Acc : SepProp} {Body : α → SepProp} {Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ v : α, SepWPp prog ret s (Acc ∗ (Body v ∗ Rest)) post Qp) :
    SepWPp prog ret s (Acc ∗ ((∃∗ v : α, Body v) ∗ Rest)) post Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left,
    satisfies_sepExists] at hm
  rcases hm with ⟨v, hm⟩
  exact h v R hm hL

private theorem sepWPp_shift_p {prog : Program} {ret : BitVec 64} {s : State}
    {Acc C Rest : SepProp} {post Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s ((Acc ∗ C) ∗ Rest) post Qp) :
    SepWPp prog ret s (Acc ∗ (C ∗ Rest)) post Qp := by
  have heq : Acc ∗ (C ∗ Rest) = (Acc ∗ C) ∗ Rest := (sepConj_assoc Acc C Rest).symm
  rw [heq]
  exact h

private theorem sepWPp_mid_5_p {prog : Program} {ret : BitVec 64} {s : State}
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

private theorem sepWPp_mid_6_p {prog : Program} {ret : BitVec 64} {s : State}
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

private theorem sepWPp_mid_11_p {prog : Program} {ret : BitVec 64} {s : State}
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

private theorem sepWP_elim_words6_exists_p {prog : Program} {pc : BitVec 64} {s : State}
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

private theorem sp_aligned_of_eq_p {s1 s2 : State} (halign : s1.spAligned = true)
    (hsp : s2.sp = s1.sp) : s2.spAligned = true := by
  simp only [State.spAligned, hsp] at halign ⊢
  exact halign

private theorem sepWP_frame_cut_pool_placed [LibsignalPlacement] {prog : Program}
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

private theorem sepWPp_frame_cut_pool_placed [LibsignalPlacement] {prog : Program}
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

private theorem sepWPp_call_cells_p [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {calleeStk : Nat} {x0 : PkPollGhost} {st0 : M.σ} {R0 : SepProp}
    {entry ret_pc : BitVec 64} {spec : Spec α} {g : α}
    {s0 s : State} {P F : SepProp}
    (hcall : subroutine_ok (lsProg_571 H) entry (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
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
      SepWPp (lsProg_571 H) (s0.readReg64 .x30) sf
        (spec.post g s sf ∗ F)
        (spkPostQ rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0)
        (spkPanicQp rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0)) :
    SepWPp (lsProg_571 H) (s0.readReg64 .x30) s P
      (spkPostQ rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0)
      (spkPanicQp rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x0 st0 R0 s0) := by
  refine SepWPp.call_lscro (pl := lsmpl) (x := g) hcall hcrl hpc hrun hsp hlr
    (fun R hm => by
      rw [← sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hP) hm)
    (fun sf code R' _ hex => by
      rw [hexit_eq] at hex
      exact not_satisfies_false_sepConj hex)
    (fun sf _ hm => by
      rw [hpan_eq, sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    hnext
    (h_no_oom := fun R' sf _ ho => by
      rw [hoom_eq] at ho
      exact (not_satisfies_false_sepConj ho).elim)

/-! ## 3. Symbolic Execution of `spkGetPollInnerSpec` on `lsProg_571 H` -/

private theorem spkGetPollInner_sepWPp_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv1 : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hDecimalCells : subroutine_ok (lsProg_571 H) (lsmpl.base 597)
      (withLsCodeRoLoaded lsmpl (decimalCellsSpec A lim DecEnv calleeStk)))
    (hDirGetCells0 : subroutine_ok (lsProg_571 H) (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl (dirGetCellsSpec rd pathOk A lim GetEnv1 s0.fs.files calleeStk)))
    (hDecodeCells : subroutine_ok (lsProg_571 H) (lsmpl.base 595)
      (withLsCodeRoLoaded lsmpl (decodeSpkCellsSpec A lim DecodeEnv calleeStk)))
    (hDeallocCells : subroutine_ok (lsProg_571 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget.deallocBufCellsSpec
          A lim calleeStk)))
    (hDropCells : subroutine_ok (lsProg_571 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget.dropSpeWordCellsSpec
          A lim calleeStk)))
    (hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 571)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.fut)
    (hx8 : s0.readReg64 .x8 = x.out)
    (hname : CryptoVerification.SignalSession.Cli.PkNameOk pathOk x.dir x.id)
    (hsize : CryptoVerification.SignalSession.Cli.PkSizeOk rd s0.fs.files x.dir x.id)
    (hfit : FitsEnv M lim st (CliSpkGetPollEnv DecEnv GetEnv1 DecodeEnv rd s0.fs.files x)) :
    SepWPp (lsProg_571 H) (s0.readReg64 .x30) s0
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 88 ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 384#64) calleeStk ∗ cells (s0.sp - 384#64) 48)
      (spkPostQ rd pathOk A lim DecEnv GetEnv1 DecodeEnv calleeStk x st R s0)
      (spkPanicQp rd pathOk A lim DecEnv GetEnv1 DecodeEnv calleeStk x st R s0) := by
  rw [cells_48_split s0.sp]
  dsimp only [spkScratch15]
  have hfront :
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 88 ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          (cells (s0.sp - 376#64) 5 ∗ cells (s0.sp - 336#64) 5 ∗ cells (s0.sp - 296#64) 5) ∗
          cells (s0.sp - 248#64) 5 ∗
          cells (s0.sp - 200#64) 6 ∗ cells (s0.sp - 152#64) 5 ∗
          cells (s0.sp - 96#64) 6 ∗ cells (s0.sp - 48#64) 6) =
      (x.fut ↦₆₄ x.self) ∗
        memRegion x.out 88 ∗
        cells (s0.sp - 376#64) 5 ∗ cells (s0.sp - 336#64) 5 ∗ cells (s0.sp - 296#64) 5 ∗
        cells (s0.sp - 248#64) 5 ∗ cells (s0.sp - 200#64) 6 ∗ cells (s0.sp - 152#64) 5 ∗
        cells (s0.sp - 96#64) 6 ∗ cells (s0.sp - 48#64) 6 ∗
        (((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
          dirAt A.repAlloc x.self x.dir ∗ A.pool lim st s0 ∗
          stackAt (s0.sp - 384#64) calleeStk ∗ spkPollSlack s0.sp) := by sep_ac_rfl
  rw [hfront]
  rw [memRegion_88_cells x.out]
  refine sepWPp_mid_11_p fun _ _ _ _ _ _ _ _ _ _ _ => sepWPp_shift_p ?_
  rw [cells_sub_5_376_eq]
  refine sepWPp_mid_5_p fun _ a1 a2 a3 a4 => sepWPp_shift_p ?_
  rw [cells_sub_5_336_eq]
  refine sepWPp_mid_5_p fun b0 b1 _ _ _ => sepWPp_shift_p ?_
  rw [cells_sub_5_296_eq]
  refine sepWPp_mid_5_p fun _ _ _ _ _ => sepWPp_shift_p ?_
  rw [cells_sub_5_248_eq]
  refine sepWPp_mid_5_p fun _ _ _ _ _ => sepWPp_shift_p ?_
  rw [cells_sub_6_200_eq]
  refine sepWPp_mid_6_p fun _ _ _ _ _ _ => sepWPp_shift_p ?_
  rw [cells_sub_5_152_eq]
  refine sepWPp_mid_5_p fun _ _ _ _ _ => sepWPp_shift_p ?_
  rw [cells_sub_6_96_eq]
  refine sepWPp_mid_6_p fun _ _ _ _ _ _ => sepWPp_shift_p ?_
  rw [cells_sub_6_48_eq]
  refine sepWPp_mid_6_p fun _ _ _ _ _ _ => ?_
  change s0.pc = (blkPl_571).base at hpc
  apply sepWPp_frame_cut_pool_placed hcrl0
    (step_entry_to_decimal_pool_placed (H := H) (A := A) (lim := lim) (st := st)
      hpc hrun hsp_align hx0 hx8)
  rintro sm1 hpcm1 hrunm1 hspm1 hcrl_sm1
    ⟨hsp1, hvr1, htr1, hfiles1, hx0_1, hx1_1, hx30_1, hx19_1, hx20_1, hx21_1, hx27_1, hx29_1⟩
  have hfit1 : FitsEnv M lim st (DecEnv x.id) := hfit.seq_left
  refine sepWPp_call_cells_p
    (g := ((x.id, s0.sp - 248#64, _, _, _, s0.sp - 384#64), st))
    hDecimalCells hcrl_sm1 hpcm1 hrunm1 hspm1 hx30_1
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (entails_pure_pre_p ⟨hx0_1, hx1_1, hsp1, hfit1⟩) ?_
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1 hcrl_sf1
  rcases csp_regs hcs_sf1 with
    ⟨hx19_f1, hx20_f1, hx21_f1, _, _, _, _, _, hx27_f1, _, hx29_f1, hvr_f1⟩
  dsimp only [decimalCellsSpec]
  refine sepWPp_elim_exists_p fun evs1 =>
    sepWPp_elim_exists_p fun nCap => sepWPp_elim_exists_p fun nPtr => ?_
  apply sepWPp_pull_pure_p
  rintro ⟨htr_sf1, hfiles_sf1, hevs1⟩
  have hfit_r1 := hfit.seq_right hevs1
  apply sepWPp_frame_cut_pool_placed hcrl_sf1
    (step_68_to_dirGet_pool_placed (H := H) (A := A) (lim := lim) (st := M.stepEvents evs1 st)
      (x := x) hpc_sf1 hrun_sf1 (sp_aligned_of_eq_p hspm1 hsp_sf1)
      (hsp_sf1.trans hsp1) (hx21_f1.trans hx21_1) (hx29_f1.trans hx29_1))
  rintro sm2 hpcm2 hrunm2 hspm2 hcrl_sm2
    ⟨hsp2, hvr2, htr2, hfiles2, hx0_2, hx1_2, hx2_2, hx3_2, hx30_2,
      hx19_2, hx20_2, hx22_2, hx27_2, hx29_2⟩
  have htr_sm2 : sm2.trace = s0.trace := htr2.trans (htr_sf1.trans htr1)
  have hfiles_sm2 : sm2.fs.files = s0.fs.files := hfiles2.trans (hfiles_sf1.trans hfiles1)
  have hfit2 : FitsEnv M lim (M.stepEvents evs1 st) (GetEnv1 x.dir x.id) := hfit_r1.seq_left
  refine sepWPp_call_cells_p
    (g := ((s0.sp - 200#64, x.self, x.dir, nCap, nPtr, x.id, _, _, _, _, _, _, s0.sp - 384#64),
      M.stepEvents evs1 st))
    hDirGetCells0 hcrl_sm2 hpcm2 hrunm2 hspm2 hx30_2
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (entails_pure_pre_p ⟨hx0_2, hx1_2, hx2_2, hx3_2, hsp2, hfiles_sm2, hname, hfit2⟩) ?_
  intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 hcs_sf2 hcrl_sf2
  rcases csp_regs hcs_sf2 with
    ⟨hx19_f2, hx20_f2, _, hx22_f2, _, _, _, _, hx27_f2, _, hx29_f2, hvr_f2⟩
  have hsp_f2 : sf2.sp = s0.sp - 384#64 := hsp_sf2.trans hsp2
  have halign_f2 : sf2.spAligned = true := sp_aligned_of_eq_p hspm2 hsp_sf2
  have hvr_s0_f2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0 :=
    hvr_f2.trans (hvr2.trans (hvr_f1.trans hvr1))
  have hx19_s0_f2 : sf2.readReg64 .x19 = x.fut :=
    hx19_f2.trans (hx19_2.trans (hx19_f1.trans hx19_1))
  have hx20_s0_f2 : sf2.readReg64 .x20 = x.out :=
    hx20_f2.trans (hx20_2.trans (hx20_f1.trans hx20_1))
  have hx22_s0_f2 : sf2.readReg64 .x22 = nPtr := hx22_f2.trans hx22_2
  have hx27_s0_f2 : sf2.readReg64 .x27 = s0.sp - 200#64 :=
    hx27_f2.trans (hx27_2.trans (hx27_f1.trans hx27_1))
  have hx29_s0_f2 : sf2.readReg64 .x29 = s0.sp - 96#64 := hx29_f2.trans hx29_2
  dsimp only [dirGetCellsSpec]
  refine sepWPp_elim_exists_p fun evs2 => sepWPp_elim_exists_p fun gr =>
    sepWPp_elim_exists_p fun g0 => sepWPp_elim_exists_p fun g1 =>
    sepWPp_elim_exists_p fun g2 => sepWPp_elim_exists_p fun g3 =>
    sepWPp_elim_exists_p fun g4 => sepWPp_elim_exists_p fun g5 => ?_
  apply sepWPp_pull_pure_p
  rintro ⟨hgr, htr_f2, hevs2⟩
  have hfit_r2 := hfit_r1.seq_right hevs2
  rcases gr with ⟨⟩ | (_ | ⟨b, bs⟩)
  · -- `gr = .error ()`
    dsimp only [dirGetDetached]
    apply sepWPp_pull_pure2_p
    intro hg0
    apply SepWPp.of_sepWP_ret
    apply sepWP_frame_cut_pool_placed hcrl_sf2
      (step_readErr_88_to_280_pool_placed (H := H) (A := A) (lim := lim)
        (st := M.stepEvents evs2 (M.stepEvents evs1 st))
        hg0 hpc_sf2 hrun_sf2 halign_f2 hsp_f2 hx27_s0_f2 hx29_s0_f2)
    rintro sm3 hpcm3 hrunm3 hspm3 hcrl_sm3
      ⟨hsp3, hvr3, htr3, hx19_3, hx20_3, hx22_3, hx25_3, hx23_3, hx24_3, hx21_3⟩
    apply sepWP_frame_cut_pool_placed hcrl_sm3
      (freeName_280_to_344_placed hDeallocCells hcrl_sm3 hpcm3 hrunm3 hspm3 hsp3
        (hx22_3.trans hx22_s0_f2))
    rintro sm4 hpcm4 hrunm4 hspm4 _
      ⟨hsp4, hvr4, htr4, hx19_4, hx20_4, hx26_4, hx25_4, hx23_4, hx24_4, hx21_4⟩
    have hansA :
        PkAns.readErr =
            pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sm4.trace = s0.trace :=
      ⟨by rw [← hgr]; rfl, htr4.trans (htr3.trans (htr_f2.trans htr_sm2))⟩
    have hevsA : CliSpkGetPollEnv DecEnv GetEnv1 DecodeEnv rd s0.fs.files x
        (evs1 ++ (evs2 ++ ([] ++ optDeallocBufEvents nCap))) :=
      SeqEnv.append hevs1
        (SeqEnv.append hevs2
          (SeqEnv.append (by rw [← hgr]; rfl) (freeOnlyEvs_optDeallocBufEvents_p nCap)))
    have hstA :
        M.stepEvents (optDeallocBufEvents nCap) (M.stepEvents evs2 (M.stepEvents evs1 st)) =
          M.stepEvents (evs1 ++ (evs2 ++ ([] ++ optDeallocBufEvents nCap))) st := by
      simp only [List.nil_append, M.stepEvents_append]
    rw [hstA]
    exact epilogue_placed_ok hpcm4 hrunm4 hspm4 hsp4
      (hvr4.trans (hvr3.trans hvr_s0_f2))
      (hx19_4.trans (hx19_3.trans hx19_s0_f2))
      (hx20_4.trans (hx20_3.trans hx20_s0_f2))
      hx26_4
      (hx25_4.trans hx25_3)
      (hx23_4.trans hx23_3)
      (hx24_4.trans hx24_3)
      (hx21_4.trans hx21_3)
      (readErr88_pack_cells A.repAlloc x.out g0 g1 g2 g3 g4 g5 _ _ _ _)
      hansA hevsA
  · -- `gr = .ok []`
    dsimp only [dirGetDetached]
    apply sepWPp_pull_pure2_p
    rintro ⟨hg0, hg3⟩
    apply SepWPp.of_sepWP_ret
    apply sepWP_frame_cut_pool_placed hcrl_sf2
      (step_missing_88_to_200_placed hDeallocCells hcrl_sf2 hg0 hg3
        hpc_sf2 hrun_sf2 halign_f2 hsp_f2 hx29_s0_f2)
    rintro sm3 hpcm3 hrunm3 hspm3 hcrl_sm3
      ⟨hsp3, hvr3, htr3, hx19_3, hx20_3, hx22_3, _, hx29_3, hx26_3⟩
    apply sepWP_frame_cut_pool_placed hcrl_sm3
      (freeName_200_to_220_placed hDeallocCells hcrl_sm3 hpcm3 hrunm3 hspm3 hsp3
        (hx22_3.trans hx22_s0_f2))
    rintro sm4 hpcm4 hrunm4 hspm4 hcrl_sm4 ⟨hsp4, hcs4, htr4⟩
    rcases csp_regs hcs4 with
      ⟨hx19_4, hx20_4, _, _, _, _, _, hx26_4, _, _, hx29_4, hvr4⟩
    apply sepWP_frame_cut_pool_placed hcrl_sm4
      (step_missing_220_to_344_pool_placed (H := H) (A := A) (lim := lim)
        (st := M.stepEvents (optDeallocBufEvents nCap)
          (M.stepEvents (optDeallocBufEvents g1) (M.stepEvents evs2 (M.stepEvents evs1 st))))
        hpcm4 hrunm4 hspm4 hsp4
        (hx29_4.trans hx29_3) (hx26_4.trans hx26_3))
    rintro sm5 hpcm5 hrunm5 hspm5 _
      ⟨hsp5, hvr5, htr5, hx19_5, hx20_5, hx26_5, hx25_5, hx23_5, hx24_5, hx21_5⟩
    have hansB :
        PkAns.missing =
            pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sm5.trace = s0.trace :=
      ⟨by rw [← hgr]; rfl,
        htr5.trans (htr4.trans (htr3.trans (htr_f2.trans htr_sm2)))⟩
    have hevsB : CliSpkGetPollEnv DecEnv GetEnv1 DecodeEnv rd s0.fs.files x
        (evs1 ++ (evs2 ++ ([] ++ (optDeallocBufEvents g1 ++ optDeallocBufEvents nCap)))) :=
      SeqEnv.append hevs1
        (SeqEnv.append hevs2
          (SeqEnv.append (by rw [← hgr]; rfl)
            (FreeOnlyEvs.append
              (freeOnlyEvs_optDeallocBufEvents_p g1)
              (freeOnlyEvs_optDeallocBufEvents_p nCap))))
    have hstB :
        M.stepEvents (optDeallocBufEvents nCap)
          (M.stepEvents (optDeallocBufEvents g1) (M.stepEvents evs2 (M.stepEvents evs1 st))) =
          M.stepEvents
            (evs1 ++ (evs2 ++ ([] ++ (optDeallocBufEvents g1 ++ optDeallocBufEvents nCap)))) st := by
      simp only [List.nil_append, M.stepEvents_append]
    rw [hstB]
    exact epilogue_placed_ok (D := emp) hpcm5 hrunm5 hspm5 hsp5
      (hvr5.trans (hvr4.trans (hvr3.trans hvr_s0_f2)))
      (hx19_5.trans (hx19_4.trans (hx19_3.trans hx19_s0_f2)))
      (hx20_5.trans (hx20_4.trans (hx20_3.trans hx20_s0_f2)))
      hx26_5 hx25_5 hx23_5 hx24_5 hx21_5
      (by rw [sepConj_emp]; exact missing88_pack_cells A.repAlloc x.out _ _ _ b0 b1 a1 a2 a3 a4)
      hansB hevsB
  · -- `gr = .ok (b :: bs)`
    have hlen_lt : (b :: bs).length < 2 ^ 32 := hsize (b :: bs) hgr.symm
    have hfit3 : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
        (DecodeEnv (b :: bs)) := by
      have hfit3_opt : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st))
          (OptSpkDecodeEnv DecodeEnv (x.dir.get rd s0.fs.files (keyName x.id))) :=
        hfit_r2.seq_left
      rwa [← hgr] at hfit3_opt
    dsimp only [dirGetDetached]
    apply sepWPp_pull_pure2_p
    rintro ⟨hg0, hg3⟩
    apply sepWPp_frame_cut_pool_placed hcrl_sf2
      (step_88_to_decodeSpk_pool_placed (H := H) (A := A) (lim := lim)
        (st := M.stepEvents evs2 (M.stepEvents evs1 st))
        hg0 hg3 hlen_lt hpc_sf2 hrun_sf2 halign_f2 hsp_f2 hx29_s0_f2)
    rintro sm3 hpcm3 hrunm3 hspm3 hcrl_sm3
      ⟨hsp3, hvr3, htr3, hx0_3, hx1_3, hx2_3, hx30_3,
        hx19_3, hx20_3, hx22_3, hx23_3, hx24_3, hx27_3, hx29_3⟩
    have htr_sm3 : sm3.trace = s0.trace := htr3.trans (htr_f2.trans htr_sm2)
    refine sepWPp_call_cells_p
      (g := ((s0.sp - 200#64, g1, g2, b :: bs, _, _, _, _, _, _, _, _, _, _, _, s0.sp - 384#64),
        M.stepEvents evs2 (M.stepEvents evs1 st)))
      hDecodeCells hcrl_sm3 hpcm3 hrunm3 hspm3 hx30_3
      (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      (entails_pure_pre_p ⟨hx0_3, hx1_3, hx2_3, hsp3, Nat.zero_lt_succ _, hlen_lt, hfit3⟩) ?_
    intro sf3 hpc_sf3 hrun_sf3 hsp_sf3 hcs_sf3 hcrl_sf3
    rcases csp_regs hcs_sf3 with
      ⟨hx19_f3, hx20_f3, _, hx22_f3, hx23_f3, hx24_f3, _, _, hx27_f3, _, hx29_f3, hvr_f3⟩
    have hsp_f3 : sf3.sp = s0.sp - 384#64 := hsp_sf3.trans hsp3
    have halign_f3 : sf3.spAligned = true := sp_aligned_of_eq_p hspm3 hsp_sf3
    have hvr_s0_f3 : calleeSavedVRegs sf3 = calleeSavedVRegs s0 :=
      hvr_f3.trans (hvr3.trans hvr_s0_f2)
    have hx19_s0_f3 : sf3.readReg64 .x19 = x.fut :=
      hx19_f3.trans (hx19_3.trans hx19_s0_f2)
    have hx20_s0_f3 : sf3.readReg64 .x20 = x.out :=
      hx20_f3.trans (hx20_3.trans hx20_s0_f2)
    have hx22_s0_f3 : sf3.readReg64 .x22 = nPtr :=
      hx22_f3.trans (hx22_3.trans hx22_s0_f2)
    have hx27_s0_f3 : sf3.readReg64 .x27 = s0.sp - 200#64 :=
      hx27_f3.trans (hx27_3.trans hx27_s0_f2)
    have hx29_s0_f3 : sf3.readReg64 .x29 = s0.sp - 96#64 := hx29_f3.trans hx29_3
    dsimp only [decodeSpkCellsSpec]
    refine sepWPp_elim_exists_p fun evs3 => sepWPp_elim_exists_p fun w0 =>
      sepWPp_elim_exists_p fun w1 => sepWPp_elim_exists_p fun w2 =>
      sepWPp_elim_exists_p fun w3 => sepWPp_elim_exists_p fun w4 =>
      sepWPp_elim_exists_p fun w5 => sepWPp_elim_exists_p fun w6 =>
      sepWPp_elim_exists_p fun w7 => sepWPp_elim_exists_p fun w8 =>
      sepWPp_elim_exists_p fun w9 => sepWPp_elim_exists_p fun w10 => ?_
    apply sepWPp_pull_pure_p
    rintro ⟨htr_f3, hevs3⟩
    have htr_s0_f3 : sf3.trace = s0.trace := htr_f3.trans htr_sm3
    have hevsC : CliSpkGetPollEnv DecEnv GetEnv1 DecodeEnv rd s0.fs.files x
        (evs1 ++ (evs2 ++ (evs3 ++ (optDeallocBufEvents g1 ++ optDeallocBufEvents nCap)))) :=
      SeqEnv.append hevs1
        (SeqEnv.append hevs2
          (SeqEnv.append (by rw [← hgr]; exact hevs3)
            (FreeOnlyEvs.append
              (freeOnlyEvs_optDeallocBufEvents_p g1)
              (freeOnlyEvs_optDeallocBufEvents_p nCap))))
    have hstC :
        M.stepEvents (optDeallocBufEvents nCap)
          (M.stepEvents (optDeallocBufEvents g1)
            (M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))) =
          M.stepEvents
            (evs1 ++ (evs2 ++ (evs3 ++ (optDeallocBufEvents g1 ++ optDeallocBufEvents nCap))))
            st := by
      simp only [M.stepEvents_append]
    rcases hdes : SignedPreKeyRecord.deserialize (b :: bs) with e | r
    · -- `.error e`
      dsimp only [decodeSpkDetached]
      apply sepWPp_pull_pure2_p
      intro hw0
      apply SepWPp.of_sepWP_ret
      apply sepWP_frame_cut_pool_placed hcrl_sf3
        (step_decodeErr_124_to_280_placed hDeallocCells hcrl_sf3 hw0
          hpc_sf3 hrun_sf3 halign_f3 hsp_f3
          (hx23_f3.trans hx23_3) (hx24_f3.trans hx24_3) hx27_s0_f3 hx29_s0_f3)
      rintro sm4 hpcm4 hrunm4 hspm4 hcrl_sm4
        ⟨hsp4, hvr4, htr4, hx19_4, hx20_4, hx22_4, hx25_4, hx23_4, hx24_4, hx21_4⟩
      apply sepWP_frame_cut_pool_placed hcrl_sm4
        (freeName_280_to_344_placed hDeallocCells hcrl_sm4 hpcm4 hrunm4 hspm4 hsp4
          (hx22_4.trans hx22_s0_f3))
      rintro sm5 hpcm5 hrunm5 hspm5 _
        ⟨hsp5, hvr5, htr5, hx19_5, hx20_5, hx26_5, hx25_5, hx23_5, hx24_5, hx21_5⟩
      have hansC1 :
          PkAns.decodeErr e =
              pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sm5.trace = s0.trace := by
        refine ⟨?_, htr5.trans (htr4.trans htr_s0_f3)⟩
        rw [← hgr]; dsimp only [pkAnsOf]; rw [hdes]
      rw [hstC]
      exact epilogue_placed_ok hpcm5 hrunm5 hspm5 hsp5
        (hvr5.trans (hvr4.trans hvr_s0_f3))
        (hx19_5.trans (hx19_4.trans hx19_s0_f3))
        (hx20_5.trans (hx20_4.trans hx20_s0_f3))
        hx26_5
        (hx25_5.trans hx25_4)
        (hx23_5.trans hx23_4)
        (hx24_5.trans hx24_4)
        (hx21_5.trans hx21_4)
        (decodeErr88_pack_cells A.repAlloc x.out e w1 w2 w3 w4 w5 w6 _ _ _ _)
        hansC1 hevsC
    · -- `.ok r`
      dsimp only [decodeSpkDetached]
      apply sepWPp_pull_pure2_p
      intro hw0
      apply SepWPp.of_sepWP_ret
      apply sepWP_frame_cut_pool_placed hcrl_sf3
        (step_found_124_to_180_pool_placed (H := H) (A := A) (lim := lim)
          (st := M.stepEvents evs3 (M.stepEvents evs2 (M.stepEvents evs1 st)))
          hw0 hpc_sf3 hrun_sf3 halign_f3 hsp_f3 hx27_s0_f3 hx29_s0_f3)
      rintro sm4 hpcm4 hrunm4 hspm4 hcrl_sm4
        ⟨hsp4, hvr4, htr4, hx19_4, hx20_4, hx22_4, hx23_4, hx24_4, hx29_4,
          hx26_4, hx25_4, hx28_4, hx21_4⟩
      apply sepWP_frame_cut_pool_placed hcrl_sm4
        (freeBytes_180_to_200_placed hDeallocCells hcrl_sm4 hpcm4 hrunm4 hspm4 hsp4
          (hx23_4.trans (hx23_f3.trans hx23_3)) (hx24_4.trans (hx24_f3.trans hx24_3)))
      rintro sm5 hpcm5 hrunm5 hspm5 hcrl_sm5 ⟨hsp5, hcs5, htr5⟩
      rcases csp_regs hcs5 with
        ⟨hx19_5, hx20_5, hx21_5, hx22_5, _, _, hx25_5, hx26_5, _, hx28_5, hx29_5, hvr5⟩
      apply sepWP_frame_cut_pool_placed hcrl_sm5
        (freeName_200_to_220_placed hDeallocCells hcrl_sm5 hpcm5 hrunm5 hspm5 hsp5
          (hx22_5.trans (hx22_4.trans hx22_s0_f3)))
      rintro sm6 hpcm6 hrunm6 hspm6 hcrl_sm6 ⟨hsp6, hcs6, htr6⟩
      rcases csp_regs hcs6 with
        ⟨hx19_6, hx20_6, hx21_6, _, _, _, hx25_6, hx26_6, _, hx28_6, hx29_6, hvr6⟩
      apply sepWP_frame_cut_pool_placed hcrl_sm6
        (step_found_220_to_344_placed hDropCells hcrl_sm6 hw0 hpcm6 hrunm6 hspm6 hsp6
          (hx29_6.trans (hx29_5.trans hx29_4))
          (hx26_6.trans (hx26_5.trans hx26_4))
          (hx25_6.trans (hx25_5.trans hx25_4))
          (hx28_6.trans (hx28_5.trans hx28_4))
          (hx21_6.trans (hx21_5.trans hx21_4)))
      rintro sm7 hpcm7 hrunm7 hspm7 _
        ⟨hsp7, hvr7, htr7, hx19_7, hx20_7, hx26_7, hx25_7, hx23_7, hx24_7, hx21_7⟩
      apply sepWP_elim_words6_exists_p
      intro _ _ _ _ _ _
      have hansC2 :
          PkAns.found r =
              pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sm7.trace = s0.trace := by
        refine ⟨?_, htr7.trans (htr6.trans (htr5.trans (htr4.trans htr_s0_f3)))⟩
        rw [← hgr]; dsimp only [pkAnsOf]; rw [hdes]
      rw [hstC]
      exact epilogue_placed_ok hpcm7 hrunm7 hspm7 hsp7
        (hvr7.trans (hvr6.trans (hvr5.trans (hvr4.trans hvr_s0_f3))))
        (hx19_7.trans (hx19_6.trans (hx19_5.trans (hx19_4.trans hx19_s0_f3))))
        (hx20_7.trans (hx20_6.trans (hx20_5.trans (hx20_4.trans hx20_s0_f3))))
        hx26_7 hx25_7 hx23_7 hx24_7 hx21_7
        (found88_pack_cells A.repAlloc x.out r w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10)
        hansC2 hevsC

theorem spkGetPollInner_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_571 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_571 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk))
    (hDec : subroutine_ok (lsProg_571 H) (lsmpl.base 595)
      (decodeSignedPreKeyPlacedSpec A lim))
    (hDrop : subroutine_ok (lsProg_571 H) (lsmpl.base 553)
      (dropSpeWordSpecPlaced A lim))
    (hFs : TraceFsSound (lsProg_571 H))
    (hhi : max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)) ≤ 2 ^ 64)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs) :
    subroutine_ok (lsProg_571 H)
      (lsmpl.base 571)
      (withLsCodeRoLoaded lsmpl
        (spkGetPollInnerSpec rd pathOk A lim DecEnv (fun dir id => GetEnv dir (keyName id))
          DecodeEnv
          (max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))))) := by
  set calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
  have hDecimalCells := decimal_cells_placed_ok hDecimal hFs (calleeStk := calleeStk) (by omega) hhi
  have hDecodeCells := decodeSpk_cells_placed_ok hDec (calleeStk := calleeStk) (by omega) hhi
    hSub hSup
  have hDeallocCells := deallocBuf_cells_placed_ok (prog := lsProg_571 H) hC
    (calleeStk := calleeStk) (by omega) hhi
  have hDropCells := dropSpeWord_cells_placed_ok hDrop (calleeStk := calleeStk) (by omega) hhi
  apply subroutine_ok_of_sepWPp_init
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl0, hpre⟩
  dsimp only [spkGetPollInnerSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize, hfit⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  exact spkGetPollInner_sepWPp_at hDecimalCells
    (dirGet_cells_placed_ok (F0 := s0.fs.files) hGet (calleeStk := calleeStk) (by omega) hhi)
    hDecodeCells hDeallocCells hDropCells hcrl0 hpc hrun hsp_align hx0 hx8 hname hsize hfit

/-- Direct `spkGetPollSpecPlaced` proof on `lsProg_571 H` accepting an arbitrary `FsFiles`-indexed
    `GetEnv` in `dirGetSpecPlaced`. -/
theorem spkGetPoll_placed_fs_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_571 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_571 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok (lsProg_571 H) (lsmpl.base 595)
      (decodeSignedPreKeyPlacedSpec A lim))
    (hDrop : subroutine_ok (lsProg_571 H) (lsmpl.base 553)
      (dropSpeWordSpecPlaced A lim))
    (hFs : TraceFsSound (lsProg_571 H))
    (hstk : 0x180 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs) :
    subroutine_ok (lsProg_571 H) (lsmpl.base 571)
      (spkGetPollSpecPlaced rd pathOk A lim
        (fun F0 x =>
          CliSpkGetPollEnv DecEnv (fun dir id => GetEnv F0 dir (keyName id)) DecodeEnv rd F0 x)
        stk) := by
  set calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
  apply subroutine_ok_of_sepWPp_init
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  unfold spkGetPollSpecPlaced pkGetPollSpecOfPlaced at hpre
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl0, hpre⟩
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize, hfit⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 88 ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 384 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
    stackAt_spkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 384))
  refine ⟨_, hmem, ?_⟩
  have hDecimalCells := decimal_cells_placed_ok hDecimal hFs (calleeStk := calleeStk)
    (by omega) hcal_hi
  have hDirGetCells0 := dirGet_cells_placed_ok (F0 := s0.fs.files) hGet (calleeStk := calleeStk)
    (by omega) hcal_hi
  have hDecodeCells := decodeSpk_cells_placed_ok hDec (calleeStk := calleeStk)
    (by omega) hcal_hi hSub hSup
  have hDeallocCells := deallocBuf_cells_placed_ok (prog := lsProg_571 H) hC
    (calleeStk := calleeStk) (by omega) hcal_hi
  have hDropCells := dropSpeWord_cells_placed_ok hDrop (calleeStk := calleeStk)
    (by omega) hcal_hi
  have hwpp := spkGetPollInner_sepWPp_at (R := F_extra ∗ R) hDecimalCells hDirGetCells0
    hDecodeCells hDeallocCells hDropCells hcrl0 hpc hrun hsp_align hx0 hx8 hname hsize hfit
  intro R' hmR' hcl
  clear hmem
  have hmR'_in : s0.mem ⊨
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 88 ∗
        A.pool lim st s0 ∗ stackAt (s0.sp - 384#64) calleeStk ∗ cells (s0.sp - 384#64) 48) ∗
      (F_extra ∗ R') := by
    dsimp only [F_extra]
    convert hmR' using 1; sep_ac_rfl
  rcases hwpp (F_extra ∗ R') hmR'_in hcl with
    ⟨sf, hsteps, ⟨hpc_f, hrun_f, P_f, hm_f, hpost, hsp_f, hcs_f⟩ |
      ⟨hpan_f, P_f, hm_f, hpan_q⟩ | ⟨_, hoom_f⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, P_f ∗ F_extra, by rwa [sepConj_assoc], ?_, hsp_f, hcs_f⟩⟩
    intro hm_fR
    have hm_in_post : sf.mem ⊨ P_f ∗ (F_extra ∗ R) := by
      simpa only [sepConj_assoc] using hm_fR
    have hq := hpost hm_in_post
    dsimp only [withLsCodeRoLoaded, spkGetPollInnerSpec, spkGetPollSpecPlaced,
      pkGetPollSpecOfPlaced, spkAnsAt, pkBoxAt] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
      stackAt_spkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_f, P_f ∗ F_extra, by rwa [sepConj_assoc], ?_⟩)⟩
    intro hm_fR
    have hq := hpan_q (by simpa only [sepConj_assoc] using hm_fR)
    dsimp only [spkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hoom_f).elim

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPlacedBudget
