/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudgetFd
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded Epilogue and Deallocation Blocks for `remove_pre_key::{closure#0}`

`FdsGe3Closed`-threaded shared epilogue and `Vec` deallocation blocks on Block `575`
(`lsProg_575 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.EpiloguePlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (PkPollGhost pkBoxAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_575 blkPl_575)
open CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
  (calleeSavedVRegs_writeVReg128_0 epilogueOut epiloguePre extractLsb_0_64_append_p
   extractLsb_64_64_append_p fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState
   fs_writeReg fs_writeReg32 fs_writeReg64 fs_writeVReg128 layoutOk_u8_of_ne_zero savedCalleeSlots
   setWidth_32_setWidth_64 setWidth_64_append_p spAligned_sub_c0 sret48_epilogue_split vecU8Tail
   vecU8_free_ne vecU8_free_zero)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudgetFd
  (pkrm_dealloc_keepsFs_placed_ok)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0 setWidth_32_setWidth_64
  extractLsb_0_64_append_p extractLsb_64_64_append_p setWidth_64_append_p
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

/-- Shared epilogue (`+0x108 .. +0x13c`) on Block `575`, syncing `A.pool lim st` and preserving `sf.fs = s.fs`. -/
theorem pkrm_epilogue_108_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : LibsignalHooks}
    (x : PkPollGhost) (st : M.σ) (s0 s : State)
    (w0 w1 w2 w3 : BitVec 64) (q_sp0 : BitVec 128)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_575).base + 264#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xc0#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = w0)
    (hx24 : s.readReg64 .x24 = w1)
    (hx25 : s.readReg64 .x25 = w2)
    (hx27 : s.readReg64 .x27 = w3)
    (hfoc : P ⊢ epiloguePre s0 x q_sp0 ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.fs = s.fs →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 q_sp0 ∗ A.pool lim st sf ∗ F) →
      post sf P_f) :
    SepWP ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_c0 hsp_align hsp
  refine SepWP.weaken_pre hfoc ?_
  unfold epiloguePre pkBoxAt savedCalleeSlots
  rw [sret48_epilogue_split x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun o0 => SepWP.exists_elim fun o1 =>
    SepWP.exists_elim fun o2 => SepWP.exists_elim fun o3 =>
    SepWP.exists_elim fun oq => ?_
  have hb8 : s0.sp - 0xc0#64 + 8#64 = s0.sp - 184#64 := by bv_omega
  unfold Arm64.pointsTo128
  simp only [hb8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine hk _ _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [CalleeSavedPreserved, arm64_norm, *]) ?_
  unfold epilogueOut savedCalleeSlots pkBoxAt Arm64.pointsTo128
  simp only [hb8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_focus

/-- Tail block at `+0x0f4 .. +0x104` on Block `575` preserving `sf.fs = s.fs`. -/
theorem pkrm_finish_f4_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H)
    (x : PkPollGhost) (st : M.σ) (s0 s : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (w0 w1 w2 w3 : BitVec 64) (q_sp0 : BitVec 128)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_575).base + 244#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xc0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = w0)
    (hx24 : s.readReg64 .x24 = w1)
    (hx25 : s.readReg64 .x25 = w2)
    (hx27 : s.readReg64 .x27 = w3)
    (hfoc : P ⊢ ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xc0#64) extHookStack ∗
      epiloguePre s0 x q_sp0 ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.fs = s.fs →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 q_sp0 ∗
        ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗
        A.pool lim (M.stepEvents (optDeallocBufEvents nameCap) st) sf ∗ F) →
      post sf P_f) :
    SepWP ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hep := @pkrm_epilogue_108_placed_fd _ M A lim H
  refine SepWP.weaken_pre hfoc ?_
  by_cases hncap : nameCap = 0#64
  · subst hncap
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil] at hk
    refine SepWP.fold (vecU8_free_zero A.repAlloc namePtr hnlen) (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrl
    wp_steps_sync_pool ((blkPl_575).base + 264#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro _hcrl_108
    refine hep x st s0 _ w0 w1 w2 w3 q_sp0 _
      (((s0.sp - 0x78#64) ↦₆₄ 0#64) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hfs_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by simp only [arm64_norm, *]))
          (hfs_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)))
  · obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
    have hlay : RustLayoutOk nameCap.toNat 1 := ⟨⟨hcap_pos, hpow1, hcap_hi⟩, by decide⟩
    have hdealloc := pkrm_dealloc_keepsFs_placed_ok hFs
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack] at hdealloc
    have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    simp only [optDeallocBufEvents, hncap, ↓reduceIte] at hk
    refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_da
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrl_da
    rcases hcrl_da with ⟨hcl_da, _⟩
    wp_call hdealloc (namePtr, nameCap.toNat, 1, st)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcrl_108
    refine hep x (M.stepEvents (rustDeallocEvents nameCap.toNat 1) st) s0 _
      w0 w1 w2 w3 q_sp0 _
      (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre; simp only [hsp, sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hfs_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by simp only [arm64_norm, *]))
          (hfs_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)))

/-- Deallocation block on nonempty bytes (`+0x06c .. +0x090`) on Block `575` preserving `sm.fs = s.fs`. -/
theorem pkrm_drop_both_6c_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFs : AllocContractsFsPlaced A lim H)
    (st : M.σ) (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {ret : BitVec 64} {post : State → SepProp → Prop}
    (hbcap : bytesCap ≠ 0#64)
    (hblen : bytesBs.length ≤ bytesCap.toNat)
    (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_575).base + 108#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xc0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx24 : s.readReg64 .x24 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hfoc : P ⊢
      bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A.repAlloc bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xc0#64) extHookStack ∗
      A.pool lim st s ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (blkPl_575).base + 148#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 0xc0#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      sm.fs = s.fs →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = bytesCap →
      sm.readReg64 .x25 = bytesPtr →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWP ((blkPC_575).rebase (blkPl_575).base H) ret sm
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          A.pool lim (M.stepEvents
            (rustDeallocEvents bytesCap.toNat 1 ++ optDeallocBufEvents nameCap) st) sm ∗ F)
        post) :
    SepWP ((blkPC_575).rebase (blkPl_575).base H) ret s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_c0 hsp_align hsp
  obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
  have hlay_b : RustLayoutOk bytesCap.toNat 1 := ⟨⟨hb_pos, hb_pow1, hb_hi⟩, by decide⟩
  have hdealloc := pkrm_dealloc_keepsFs_placed_ok hFs
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack] at hdealloc
  have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
  refine SepWP.weaken_pre hfoc ?_
  refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := bytesPtr) hbcap hblen hblt) (by sep_focus) ?_
  apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_da1
  apply sepWP_seq_lscro (mid := (blkPl_575).base + 128#64) hcrl_da1
  rcases hcrl_da1 with ⟨hcl_da1, _⟩
  wp_call hdealloc (bytesPtr, bytesCap.toNat, 1, st)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_80
  by_cases hncap : nameCap = 0#64
  · subst hncap
    refine SepWP.fold (vecU8_free_zero A.repAlloc namePtr hnlen) (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 148#64) hcrl_80
    wp_steps_sync_pool ((blkPl_575).base + 148#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_94
    refine SepWP.weaken_pre
      (Entails.of_eq (by
        simp only [optDeallocBufEvents, ↓reduceIte, List.append_nil, arm64_norm, *]
        sep_ac_rfl))
      (hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) hcrl_94 (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
  · obtain ⟨hn_pos, hn_pow1, hn_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
    have hlay_n : RustLayoutOk nameCap.toNat 1 := ⟨⟨hn_pos, hn_pow1, hn_hi⟩, by decide⟩
    have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl_80
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_da2
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 148#64) hcrl_da2
    rcases hcrl_da2 with ⟨hcl_da2, _⟩
    wp_call hdealloc (namePtr, nameCap.toNat, 1, M.stepEvents (rustDeallocEvents bytesCap.toNat 1) st)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_94
    refine SepWP.weaken_pre
      (Entails.of_eq (by
        simp only [optDeallocBufEvents, ↓reduceIte, ← M.stepEvents_append, arm64_norm, *]
        sep_ac_rfl))
      (hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) hcrl_94 (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.EpiloguePlacedBudgetFd
