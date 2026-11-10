/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Segment 4 (`ct1.reserve(128)`)

Proves `[LibsignalPlacement]` and fixed-base `RustCliAllocBudget`-threaded Segment 4
(`+656 → +676` + slow path `+1036..+1060`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsReserveBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347 libsignalSessionCode lsmpl
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall doReserveStack extHookStack finishGrowStack reserveCap tripleRatchetProgAtExt
)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name
)
open CryptoVerification.SpqrV1.Unchunked (
  cap_ne_zero_of_add_128_le fold_vecU8At_sp_304 le_of_not_ule_sub_len
  reserveCap_bound_of_ule_sub_len reserveCap_ge_add_128 reserveCap_ne_zero_len
  stackAt_extHook_eq_doReserve vecU8At_expose_sp_304_cells_heap
  vecU8At_expose_sp_304_of_ne_zero vecU8HeapAt vecU8HeapAt_expose_of_ne_zero
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedSendCt2PreEnv doReserve7_ok_at_sendCt2
  doReserveEvents_128_eq fitsEnv_doReserve128_of_fitsEvents
  fitsEvents_reserve128_of_preEnv sendCt2Reserve128Events sendCt2Seg23Events
  sepWPp_call_noPanic sepWPp_exists_left_eq sepWPp_fold_eq sepWPp_intro_state
  sepWPp_pure_left_eq sepWPp_rw_pre_eq
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setMem_setPC_pre

private theorem ule_127_add_le {cap : BitVec 64} {len : Nat}
    (hle : len ≤ cap.toNat) (hlen : len < 2 ^ 32)
    (h : (cap - BitVec.ofNat 64 len).ule 127#64 = true) :
    cap.toNat ≤ len + 127 := by
  have hlen_bv : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.ule_eq_decide, decide_eq_true_eq, BitVec.toNat_sub_of_le] at h
  · rw [hlen_bv] at h
    change cap.toNat - len ≤ 127 at h
    omega
  · rw [BitVec.le_def, hlen_bv]
    exact hle

/-! ## Segment 4: `ct1.reserve(128)` (`+656 → +676` + slow path `+1036..+1060`) -/

/-- Relocatable `[LibsignalPlacement]` budget-threaded `ct1.reserve(128)` (`+656 → +676`),
    polymorphic over `{Q Qp : State → SepProp → Prop}`. -/
theorem send_ct2_reserve_ct1_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hFit : ∀ cap : BitVec 64, x.st.ct1.length ≤ cap.toNat → cap.toNat ≤ x.st.ct1.length + 127 →
      FitsEvents M lim stCost (sendCt2Reserve128Events cap x.st.ct1.length))
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_347).base + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (blkPl_347).base + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool lim (M.stepEvents evsRes stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim stCost st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  refine sepWPp_fold_eq
    (A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (vecU8At_expose_sp_304_cells_heap A.repAlloc s0.sp cap_ct1 ptr_ct1 x.st.ct1)
    (by sep_ac_rfl) ?_
  refine sepWPp_pure_left_eq (φ := x.st.ct1.length ≤ cap_ct1.toNat ∧ cap_ct1.toNat < 2 ^ 63 ∧ ptr_ct1 ≠ 0#64)
    (((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
      vecU8HeapAt A.repAlloc cap_ct1 ptr_ct1 x.st.ct1 ∗
      A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by sep_ac_rfl) ?_
  rintro ⟨hct1_le, hct1_lt, hptr_ct1_ne⟩
  by_cases hls : ¬ (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true
  · have hls_f : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = false :=
      Bool.eq_false_iff.mpr hls
    have hge128 : x.st.ct1.length + 128 ≤ cap_ct1.toNat :=
      le_of_not_ule_sub_len hct1_le hct1_lt hls
    have hcap_ct1_ne : cap_ct1 ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
    refine sepWPp_fold_eq
      (((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (vecU8HeapAt_expose_of_ne_zero A.repAlloc cap_ct1 ptr_ct1 x.st.ct1 hcap_ct1_ne)
      (by sep_ac_rfl) ?_
    refine sepWPp_pure_left_eq (φ := x.st.ct1.length ≤ cap_ct1.toNat ∧ cap_ct1.toNat < 2 ^ 63 ∧ ptr_ct1 ≠ 0#64)
      ((ptr_ct1 ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1 + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1 cap_ct1.toNat 1 ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (by simp only [RustCliAllocBudget.repAlloc_live]; sep_ac_rfl) ?_
    intro _
    wp_steps_sync_pool ((blkPl_347).base + 676#64)
    simp only [State.setMem_setMem]
    refine sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 []
        (SendCt2Reserve128Env.nil x.st.ct1.length)
        hcap_ct1_ne hge128 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hls_t : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true :=
      Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_len hct1_le hct1_lt32 hls_t
    have hhi := ule_127_add_le hct1_le hct1_lt32 hls_t
    have hFitSlow := fitsEnv_doReserve128_of_fitsEvents
      (v := s0.sp - 304#64) (ptr := ptr_ct1) (hFit cap_ct1 hct1_le hhi)
    wp_steps_sync_pool (lsmpl.base 320)
    simp only [State.setMem_setMem]
    refine sepWPp_intro_state fun s_call hs_call => ?_
    rw [← hs_call]
    refine sepWPp_fold_eq
      (A.pool lim stCost s_call ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (fold_vecU8At_sp_304 A.repAlloc s0.sp cap_ct1 ptr_ct1 x.st.ct1)
      (by sep_ac_rfl) ?_
    have hstack_res :
        stackAt (s0.sp - 336#64) extHookStack ⊢
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack :=
      Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp)
    refine sepWPp_fold_eq
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim stCost s_call ∗ F_frame)
      hstack_res (by sep_ac_rfl) ?_
    have hsp_call : s_call.sp = s0.sp - 336#64 := by
      simp only [hs_call, State.sp, wp_norm, arm64_norm, *]
    refine sepWPp_call_noPanic h_res
      (⟨s0.sp - 304#64, cap_ct1, ptr_ct1, x.st.ct1, 128⟩, stCost)
      (memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
      (by rw [hs_call]; wp_norm_goal)
      (by simp only [hs_call, wp_norm, arm64_norm, *])
      (by rw [State.spAligned, hsp_call]; exact hfsp_align)
      (ret_pc := (blkPl_347).base + 1056#64)
      (by simp only [hs_call, Reg.lr, wp_norm, arm64_norm, *])
      ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    · intro R' hm
      dsimp only [doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [hsp_call, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, hbound, hFitSlow⟩, ?_⟩
      · simp only [hs_call, Reg.x0, wp_norm, arm64_norm, *]
      · simp only [hs_call, Reg.x1, wp_norm, arm64_norm, BitVec.toNat_ofNat, *]
        omega
      · simp only [hs_call, Reg.x2, wp_norm, arm64_norm, BitVec.toNat_ofNat, *]
      · simp only [hs_call, Reg.x3, wp_norm, arm64_norm, *]
      · simp only [hs_call, Reg.x4, wp_norm, arm64_norm, *]
      · dsimp only [doReserveStack] at hm
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
    · dsimp only [doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [hsp_call, doReserveEvents_128_eq]
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
        hx27_1, hx28_1, hfp_1, hvregs_1⟩
      simp only [hs_call, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      simp only [hs_call, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
      refine sepWPp_pure_left_eq (φ := sf1.trace = s_call.trace)
        ((∃∗ ptr_ct1' : BitVec 64,
            vecU8At A.repAlloc (s0.sp - 304#64)
              (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
              ptr_ct1' x.st.ct1) ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by dsimp only [doReserveStack]; sep_ac_rfl) ?_
      intro htr1
      have htr1' : sf1.trace = s0.trace := by
        simpa only [hs_call, wp_norm, arm64_norm, htr] using htr1
      refine sepWPp_exists_left_eq
        (A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by sep_ac_rfl) fun ptr_ct1' => ?_
      have hcap_ct1'_ne : BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128) ≠ 0#64 :=
        reserveCap_ne_zero_len hbound
      refine sepWPp_fold_eq
        (A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (vecU8At_expose_sp_304_of_ne_zero A.repAlloc s0.sp
          (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
          ptr_ct1' x.st.ct1 hcap_ct1'_ne)
        (by sep_ac_rfl) ?_
      refine sepWPp_pure_left_eq
        (φ := x.st.ct1.length ≤ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat ∧
          (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat < 2 ^ 63 ∧ ptr_ct1' ≠ 0#64)
        (((s0.sp - 304#64) ↦₆₄ BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
            ((BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by simp only [RustCliAllocBudget.repAlloc_live]; sep_ac_rfl) ?_
      rintro ⟨_, hmax_ct1', hptr_ct1'_ne⟩
      have hge128' :
          x.st.ct1.length + 128 ≤
            (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat :=
        reserveCap_ge_add_128 hbound
      have hsp1' : sf1.sp = s0.sp - 336#64 := hsp1.trans hsp_call
      have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1'
      simp only [wp_norm, arm64_norm] at hsp1_norm
      wp_steps_sync_pool ((blkPl_347).base + 676#64)
      simp only [State.setMem_setMem]
      refine sepWPp_intro_state fun sf2 hsf2 => ?_
      rw [← hsf2]
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp).symm
      refine sepWPp_fold_eq
        (((s0.sp - 304#64) ↦₆₄ BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
            ((BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf2 ∗
          F_frame)
        hstack_back (by sep_ac_rfl) ?_
      refine sepWPp_rw_pre_eq (by sep_ac_rfl)
        (hcont sf2 (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ptr_ct1'
          (sendCt2Reserve128Events cap_ct1 x.st.ct1.length)
          (SendCt2Reserve128Env.slow hct1_le hhi)
          hcap_ct1'_ne hge128' hmax_ct1' hptr_ct1'_ne
          (by rw [hsf2]; wp_norm_goal) (by rw [hsf2]; wp_norm_goal)
          (by simp only [hsf2, State.sp, wp_norm, arm64_norm, *])
          (by simp only [hsf2, wp_norm, arm64_norm, *])
          (by simp only [hsf2, wp_norm, arm64_norm, hvregs_1, hvregs])
          (by simp only [hsf2, Reg.x1, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x29, wp_norm, arm64_norm, *]))

theorem send_ct2_reserve_ct1_placed_preEnv_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec M A lim))
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_347).base + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (blkPl_347).base + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine send_ct2_reserve_ct1_placed_wpp h_res x (M.stepEvents (sendCt2Seg23Events x.st.es) st0)
    cap_ct1 ptr_ct1 s0 st F_frame
    (fun _ hle hhi => fitsEvents_reserve128_of_preEnv hPre hle hhi)
    hct1_lt32 hpc hrun hsp hsp_s0 htr hvregs ?_
  intro st' cap_ct1' ptr_ct1' evsRes hRes
  rw [← M.stepEvents_append]
  exact hcont st' cap_ct1' ptr_ct1' evsRes hRes

/-- Fixed-base budget-threaded `ct1.reserve(128)` (`+656 → +676`) on `tripleRatchetProgAtExt b ext`
    under `AllocContracts4K b A lim ext`, polymorphic over `{Q Qp : State → SepProp → Prop}`. -/
theorem send_ct2_reserve_ct1_wpp {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hFit : ∀ cap : BitVec 64, x.st.ct1.length ≤ cap.toNat → cap.toNat ≤ x.st.ct1.length + 127 →
      FitsEvents M lim stCost (sendCt2Reserve128Events cap x.st.ct1.length))
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool lim (M.stepEvents evsRes stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim stCost st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  have h_res := doReserve7_ok_at_sendCt2 hA
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm
  clear hA
  send_ct2_fetches_range b trapHooks 656 20
  send_ct2_fetches_range b trapHooks 1036 28
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at *
  simp +singlePass only [Program.fnAddr_rebase,
    SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, subroutine_ok, SepWPp]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  generalize_entry libsignalSessionCode = codeProg
    reverting [Program.fetch, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine sepWPp_fold_eq
    (A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (vecU8At_expose_sp_304_cells_heap A.repAlloc s0.sp cap_ct1 ptr_ct1 x.st.ct1)
    (by sep_ac_rfl) ?_
  refine sepWPp_pure_left_eq (φ := x.st.ct1.length ≤ cap_ct1.toNat ∧ cap_ct1.toNat < 2 ^ 63 ∧ ptr_ct1 ≠ 0#64)
    (((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
      ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
      vecU8HeapAt A.repAlloc cap_ct1 ptr_ct1 x.st.ct1 ∗
      A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by sep_ac_rfl) ?_
  rintro ⟨hct1_le, hct1_lt, hptr_ct1_ne⟩
  by_cases hls : ¬ (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true
  · have hls_f : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = false :=
      Bool.eq_false_iff.mpr hls
    have hge128 : x.st.ct1.length + 128 ≤ cap_ct1.toNat :=
      le_of_not_ule_sub_len hct1_le hct1_lt hls
    have hcap_ct1_ne : cap_ct1 ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
    refine sepWPp_fold_eq
      (((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (vecU8HeapAt_expose_of_ne_zero A.repAlloc cap_ct1 ptr_ct1 x.st.ct1 hcap_ct1_ne)
      (by sep_ac_rfl) ?_
    refine sepWPp_pure_left_eq (φ := x.st.ct1.length ≤ cap_ct1.toNat ∧ cap_ct1.toNat < 2 ^ 63 ∧ ptr_ct1 ≠ 0#64)
      ((ptr_ct1 ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1 + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1 cap_ct1.toNat 1 ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1) ∗ ((s0.sp - 296#64) ↦₆₄ ptr_ct1) ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (by simp only [RustCliAllocBudget.repAlloc_live]; sep_ac_rfl) ?_
    intro _
    wp_steps_rebase_pool (fnBase + 676#64)
    refine sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hcont _ cap_ct1 ptr_ct1 []
        (SendCt2Reserve128Env.nil x.st.ct1.length)
        hcap_ct1_ne hge128 hct1_lt hptr_ct1_ne
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hls_t : (cap_ct1 - BitVec.ofNat 64 x.st.ct1.length).ule 127#64 = true :=
      Classical.not_not.mp hls
    have hbound := reserveCap_bound_of_ule_sub_len hct1_le hct1_lt32 hls_t
    have hhi := ule_127_add_le hct1_le hct1_lt32 hls_t
    have hFitSlow := fitsEnv_doReserve128_of_fitsEvents
      (v := s0.sp - 304#64) (ptr := ptr_ct1) (hFit cap_ct1 hct1_le hhi)
    wp_steps_rebase_pool
      (fnBase + (bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") -
        bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")))
    refine sepWPp_intro_state fun s_call hs_call => ?_
    rw [← hs_call]
    refine sepWPp_fold_eq
      (A.pool lim stCost s_call ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      (fold_vecU8At_sp_304 A.repAlloc s0.sp cap_ct1 ptr_ct1 x.st.ct1)
      (by sep_ac_rfl) ?_
    have hstack_res :
        stackAt (s0.sp - 336#64) extHookStack ⊢
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack :=
      Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp)
    refine sepWPp_fold_eq
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim stCost s_call ∗ F_frame)
      hstack_res (by sep_ac_rfl) ?_
    have hsp_call : s_call.sp = s0.sp - 336#64 := by
      simp only [hs_call, State.sp, wp_norm, arm64_norm, *]
    refine sepWPp_call_noPanic h_res
      (⟨s0.sp - 304#64, cap_ct1, ptr_ct1, x.st.ct1, 128⟩, stCost)
      (memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
      (by rw [hs_call]; wp_norm_goal)
      (by simp only [hs_call, wp_norm, arm64_norm, *])
      (by rw [State.spAligned, hsp_call]; exact hfsp_align)
      (ret_pc := fnBase + 1056#64)
      (by simp only [hs_call, Reg.lr, wp_norm, arm64_norm, *])
      ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    · intro R' hm
      dsimp only [doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [hsp_call, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, hbound, hFitSlow⟩, ?_⟩
      · simp only [hs_call, Reg.x0, wp_norm, arm64_norm, *]
      · simp only [hs_call, Reg.x1, wp_norm, arm64_norm, BitVec.toNat_ofNat, *]
        omega
      · simp only [hs_call, Reg.x2, wp_norm, arm64_norm, BitVec.toNat_ofNat, *]
      · simp only [hs_call, Reg.x3, wp_norm, arm64_norm, *]
      · simp only [hs_call, Reg.x4, wp_norm, arm64_norm, *]
      · dsimp only [doReserveStack] at hm
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
    · dsimp only [doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveSpecWithStack]
      rw [hsp_call, doReserveEvents_128_eq]
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
        hx27_1, hx28_1, hfp_1, hvregs_1⟩
      simp only [hs_call, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      simp only [hs_call, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
      refine sepWPp_pure_left_eq (φ := sf1.trace = s_call.trace)
        ((∃∗ ptr_ct1' : BitVec 64,
            vecU8At A.repAlloc (s0.sp - 304#64)
              (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
              ptr_ct1' x.st.ct1) ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by dsimp only [doReserveStack]; sep_ac_rfl) ?_
      intro htr1
      have htr1' : sf1.trace = s0.trace := by
        simpa only [hs_call, wp_norm, arm64_norm, htr] using htr1
      refine sepWPp_exists_left_eq
        (A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by sep_ac_rfl) fun ptr_ct1' => ?_
      have hcap_ct1'_ne : BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128) ≠ 0#64 :=
        reserveCap_ne_zero_len hbound
      refine sepWPp_fold_eq
        (A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (vecU8At_expose_sp_304_of_ne_zero A.repAlloc s0.sp
          (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128))
          ptr_ct1' x.st.ct1 hcap_ct1'_ne)
        (by sep_ac_rfl) ?_
      refine sepWPp_pure_left_eq
        (φ := x.st.ct1.length ≤ (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat ∧
          (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat < 2 ^ 63 ∧ ptr_ct1' ≠ 0#64)
        (((s0.sp - 304#64) ↦₆₄ BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
            ((BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf1 ∗
          stackAt (s0.sp - 336#64) doReserveStack ∗
          memRegion (s0.sp - 16720#64) 12176 ∗ F_frame)
        (by simp only [RustCliAllocBudget.repAlloc_live]; sep_ac_rfl) ?_
      rintro ⟨_, hmax_ct1', hptr_ct1'_ne⟩
      have hge128' :
          x.st.ct1.length + 128 ≤
            (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat :=
        reserveCap_ge_add_128 hbound
      have hsp1' : sf1.sp = s0.sp - 336#64 := hsp1.trans hsp_call
      have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1'
      simp only [wp_norm, arm64_norm] at hsp1_norm
      wp_steps_rebase_pool (fnBase + 676#64)
      refine sepWPp_intro_state fun sf2 hsf2 => ?_
      rw [← hsf2]
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12176 ∗ stackAt (s0.sp - 336#64) doReserveStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_doReserve s0.sp).symm
      refine sepWPp_fold_eq
        (((s0.sp - 304#64) ↦₆₄ BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)
            ((BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)).toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Reserve128Events cap_ct1 x.st.ct1.length) stCost) sf2 ∗
          F_frame)
        hstack_back (by sep_ac_rfl) ?_
      refine sepWPp_rw_pre_eq (by sep_ac_rfl)
        (hcont sf2 (BitVec.ofNat 64 (reserveCap cap_ct1.toNat x.st.ct1.length 128)) ptr_ct1'
          (sendCt2Reserve128Events cap_ct1 x.st.ct1.length)
          (SendCt2Reserve128Env.slow hct1_le hhi)
          hcap_ct1'_ne hge128' hmax_ct1' hptr_ct1'_ne
          (by rw [hsf2]; wp_norm_goal) (by rw [hsf2]; wp_norm_goal)
          (by simp only [hsf2, State.sp, wp_norm, arm64_norm, *])
          (by simp only [hsf2, wp_norm, arm64_norm, *])
          (by simp only [hsf2, wp_norm, arm64_norm, hvregs_1, hvregs])
          (by simp only [hsf2, Reg.x1, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [hsf2, Reg.x29, wp_norm, arm64_norm, *]))

theorem send_ct2_reserve_ct1_preEnv_wpp {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ)
    (cap_ct1 ptr_ct1 : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hct1_lt32 : x.st.ct1.length < 2 ^ 32)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 656#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hcont : ∀ (st' : State) (cap_ct1' ptr_ct1' : BitVec 64) (evsRes : List AllocEvent),
      SendCt2Reserve128Env x.st.ct1.length evsRes →
      cap_ct1' ≠ 0#64 →
      x.st.ct1.length + 128 ≤ cap_ct1'.toNat →
      cap_ct1'.toNat < 2 ^ 63 →
      ptr_ct1' ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 676#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          (ptr_ct1' ↦ₛ x.st.ct1) ∗
          memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es ++ evsRes) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (vecU8At A.repAlloc (s0.sp - 304#64) cap_ct1 ptr_ct1 x.st.ct1 ∗
        A.pool lim (M.stepEvents (sendCt2Seg23Events x.st.es) st0) st ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      Q Qp := by
  refine send_ct2_reserve_ct1_wpp hA x (M.stepEvents (sendCt2Seg23Events x.st.es) st0)
    cap_ct1 ptr_ct1 s0 st F_frame
    (fun _ hle hhi => fitsEvents_reserve128_of_preEnv hPre hle hhi)
    hct1_lt32 hpc hrun hsp hsp_s0 htr hvregs ?_
  intro st' cap_ct1' ptr_ct1' evsRes hRes
  rw [← M.stepEvents_append]
  exact hcont st' cap_ct1' ptr_ct1' evsRes hRes

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsReserveBudget
