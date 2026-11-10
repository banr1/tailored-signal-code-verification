/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
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
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Segment 2

Re-exports `SendCt2StepsBudgetAux` and `SendCt2StepsReserveBudget`, and proves
`[LibsignalPlacement]` and fixed-base `RustCliAllocBudget`-threaded Segment 2 (`+136 → +552`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_347 blkPl_347 libsignalSessionCode
  lsLogFilterAddr lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack sessionMemcpyRegionSpec sessionShimSpec tripleRatchetProgAtExt withStack
)
open CryptoVerification.LibsignalSpqrV1 (
  flipEndiannessOfEncapsulationStateBytes issue1275NeedsFlip
)
open CryptoVerification.SpqrV1.Alloc (
  spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym
)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name
)
open CryptoVerification.SpqrV1.Unchunked (
  es_scan_split es_swap_join es_swap_split sendCt2EsWorkAt stackAt_extHook_eq_allocHook
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliAllocNoOomSpecBase subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  UnchunkedSendCt2PreEnv allocNoOom_ok_at_sendCt2
  fitsEvents_flipAlloc_of_preEnv memcpy_ok_at_sendCt2
  scan_loop_false_placed_pool_ok scan_loop_true_placed_pool_ok sendCt2FlipAllocEvents
  sepWPp_call_noPanic sepWPp_fold_eq sepWPp_intro_state sepWPp_pure_left_eq
  sepWPp_rw_pre_eq sepWPp_weaken_pre shim_ok_at_sendCt2 swap_loop_placed_pool_ok
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  Ct1SentEkReceived
  sendCt2FlipAllocEvents
  sendCt2FlipDeallocEvents
  sendCt2Seg23Events
  sendCt2Reserve128Events
  SendCt2Reserve128Env
  sendCt2ConcatHmacEvents
  UnchunkedSendCt2PreEnv
  UnchunkedSendCt2PostEnv
  UnchunkedSendCt2Env
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
  UnchunkedCt1SentEkReceivedSendCt2PlacedOk
  sendCt2PlacedPostQOfPostEnv
  sendCt2PlacedPostQOfEnv
  sendCt2PlacedPostQ
  sendCt2PlacedPostQp
  unchunkedCt1SentEkReceivedSendCt2SpecOfPrePostEnv
  unchunkedCt1SentEkReceivedSendCt2SpecOfEnv
  unchunkedCt1SentEkReceivedSendCt2Spec
  sendCt2PostQOfPostEnv
  sendCt2PostQOfEnv
  sendCt2PostQ
  sendCt2PostQp
  libcruxHmacSafeBudgetSpec
  subroutine_ok_libcruxHmacSafe_of_budget
  libcrux_hmac_safe_placed_ok
  mlkem_encaps2_vm_placed_ok
  mlkem_encaps2_vm_ok_at_ext
  libcrux_hmac_safe_budget_ok_at_ext
  shim_ok_at_sendCt2
  alloc_ok_at_sendCt2
  allocNoOom_ok_at_sendCt2
  dealloc_ok_at_sendCt2
  memcpy_ok_at_sendCt2
  doReserve7_ok_at_sendCt2
  sliceConcat3_ok_at_sendCt2
  swap_loop_placed_ok
  swap_loop_placed_pool_ok
  scan_loop_false_placed_ok
  scan_loop_false_placed_pool_ok
  scan_loop_true_placed_ok
  scan_loop_true_placed_pool_ok
  send_ct2_prologue_to_scan_placed
  send_ct2_prologue_to_scan_placed_pool
  send_ct2_prologue_to_scan_vm
  send_ct2_prologue_to_scan_pool
)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsReserveBudget (
  send_ct2_reserve_ct1_placed_wpp
  send_ct2_reserve_ct1_placed_preEnv_wpp
  send_ct2_reserve_ct1_wpp
  send_ct2_reserve_ct1_preEnv_wpp
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

/-! ## Segment 2: Scan + Optional Issue-1275 Flip (`+136 → +552`, including `+472 → +516`) -/

private theorem call_rustAllocNoOom_cs_wppBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliAllocNoOomSpecBase M A lim false))
    (size align : Nat) (stCost : M.σ)
    (hlay : RustLayoutOk size align)
    (hFit : FitsEvents M lim stCost (rustAllocEvents size align))
    {s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → AllocCallPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → (sf.readReg64 .x0).toNat % align = 0 →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliAllocNoOomSpecBase]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hFit⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustCliAllocNoOomSpecBase]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp]
    refine sepWPp_pure_left_eq
      ((A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, hmod, hne⟩
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hacp hne hmod)

private theorem call_rustAllocNoOom_cs_wpp [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {fnAddr ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog fnAddr (rustCliAllocNoOomSpec M A lim false))
    (size align : Nat) (stCost : M.σ)
    (hlay : RustLayoutOk size align)
    (hFit : FitsEvents M lim stCost (rustAllocEvents size align))
    {s : State} {sp_call : BitVec 64} {P : SepProp} (Frame : SepProp)
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = fnAddr) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : (s.readReg64 Reg.x0).toNat = size) (hx1 : (s.readReg64 Reg.x1).toNat = align)
    (hsplit : P = (A.pool lim stCost s ∗ stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → AllocCallPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → (sf.readReg64 .x0).toNat % align = 0 →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 .x0) size align ∗
          memRegion (sf.readReg64 .x0) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
          stackAt sp_call allocHookStack) ∗ Frame) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog target_pc s P Q Qp oom := by
  refine sepWPp_call_noPanic hcall (size, align, stCost) Frame
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay, hFit, hlr.symm ▸ hlr_ls⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, hsp]
    refine sepWPp_pure_left_eq
      ((A.pool lim (M.stepEvents (rustAllocEvents size align) stCost) sf ∗
        stackAt sp_call allocHookStack ∗
        A.live (sf.readReg64 .x0) size align ∗
        memRegion (sf.readReg64 .x0) size) ∗ Frame)
      (by sep_ac_rfl) ?_
    rintro ⟨hacp, hmod, hne⟩
    exact sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hacp hne hmod)

/-- Relocatable `[LibsignalPlacement]` budget-threaded 2080-byte workspace allocation and `memcpy`
    (`+472 → +516`), discharging the OOM branch via `FitsEvents M lim stCost (rustAllocEvents 2080 1)`. -/
theorem send_ct2_5d8_to_604_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hFit : FitsEvents M lim stCost (rustAllocEvents 2080 1))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 472#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      esWorkPtr ≠ 0#64 →
      st'.pc = (blkPl_347).base + 516#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x8 = 0#64 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = 2080#64 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ x.st.es) ∗
          A.live esWorkPtr 2080 1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp := by
  have hallocNoOom := subroutine_ok_allocNoOom_of_budget halloc
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_shim hs_shim => ?_
  rw [← hs_shim]
  have hsp_shim : s_shim.sp = s0.sp - 336#64 := by
    simp only [hs_shim, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_noPanic hshim ()
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_shim ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by rw [hs_shim]; wp_norm_goal)
    (by simp only [hs_shim, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_shim]; exact hfsp_align)
    (ret_pc := (blkPl_347).base + 476#64)
    (by simp only [hs_shim, Reg.lr, wp_norm, arm64_norm, *])
    (fun R' hm => by
      dsimp only [rustAllocShimVmSpec]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by simp only [emp_sepConj]; sep_ac_rfl)) hm)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_shim hpc_shim hrun_shim hsp_shim_rel hcs_shim => ?_)
  dsimp only [rustAllocShimVmSpec]
  refine sepWPp_pure_left_eq (φ := AllocCallPreserved s_shim sf_shim ∧ VmPreserved s_shim sf_shim)
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_shim ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by sep_ac_rfl) ?_
  rintro ⟨hacp_shim, hvm_shim⟩
  rw [← A.pool_of_vmPreserved hvm_shim]
  rcases hcs_shim with ⟨hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s,
    hx27_s, hx28_s, hfp_s, hvregs_s⟩
  simp only [hs_shim, wp_norm, arm64_norm] at hx19_s hx20_s hx21_s hx22_s hx23_s hx24_s
  simp only [hs_shim, wp_norm, arm64_norm] at hx25_s hx26_s hx27_s hx28_s hfp_s hvregs_s
  have htr_shim : sf_shim.trace = s0.trace := by
    have ht := hacp_shim.2.1
    simpa only [hs_shim, wp_norm, arm64_norm, htr] using ht
  have hsp_sf_shim : sf_shim.sp = s0.sp - 336#64 := hsp_shim_rel.trans hsp_shim
  have hsp_sf_shim_norm : sf_shim.readReg64 .sp = s0.sp - 336#64 := hsp_sf_shim
  simp only [wp_norm, arm64_norm] at hsp_sf_shim_norm
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_alloc hs_alloc => ?_
  rw [← hs_alloc]
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine sepWPp_fold_eq
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_alloc ∗ F_frame)
    hstack_alloc (by sep_ac_rfl) ?_
  have hlay_2080 : RustLayoutOk 2080 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine call_rustAllocNoOom_cs_wpp hallocNoOom 2080 1 stCost hlay_2080 hFit
    (memRegion (s0.sp - 16720#64) 12288 ∗ (esPtr ↦ₛ x.st.es) ∗ F_frame)
    (ret_pc := (blkPl_347).base + 488#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_alloc]; wp_norm_goal)
    (by simp only [hs_alloc, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_alloc, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x1, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 hacp1 hne1 _ => ?_)
  have htr1 : sf1.trace = s_alloc.trace := hacp1.2.1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
    hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [hs_alloc, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [hs_alloc, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1 htr1
  have htr1' : sf1.trace = s0.trace := htr1.trans htr_shim
  have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hne1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  have hstack_back :
      memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
        stackAt (s0.sp - 336#64) extHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
  refine sepWPp_fold_eq
    (A.live (sf1.readReg64 .x0) 2080 1 ∗
      memRegion (sf1.readReg64 .x0) 2080 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) sf1 ∗
      (esPtr ↦ₛ x.st.es) ∗ F_frame)
    hstack_back (by sep_ac_rfl) ?_
  have hmr_es :
      memRegion (sf1.readReg64 .x0) 2080 ⊢
        memRegion (sf1.readReg64 .x0) x.st.es.length := by
    rw [hes_len]; exact Entails.refl _
  refine sepWPp_fold_eq
    (stackAt (s0.sp - 336#64) extHookStack ∗
      A.live (sf1.readReg64 .x0) 2080 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) sf1 ∗
      (esPtr ↦ₛ x.st.es) ∗ F_frame)
    hmr_es (by sep_ac_rfl) ?_
  wp_steps_sync_pool (lsρ spqrMemcpySym)
  simp only [State.setMem_setMem]
  refine sepWPp_intro_state fun s_mc hs_mc => ?_
  rw [← hs_mc]
  have hsp_mc : s_mc.sp = s0.sp - 336#64 := by
    simp only [hs_mc, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_noPanic hmemcpy
    (sf1.readReg64 .x0, esPtr, x.st.es)
    (stackAt (s0.sp - 336#64) extHookStack ∗
      A.live (sf1.readReg64 .x0) 2080 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s_mc ∗ F_frame)
    (by rw [hs_mc]; wp_norm_goal)
    (by simp only [hs_mc, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_mc]; exact hfsp_align)
    (ret_pc := (blkPl_347).base + 512#64)
    (by simp only [hs_mc, Reg.lr, wp_norm, arm64_norm, *])
    ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_mc hpc_mc hrun_mc hsp_mc_rel hcs_mc => ?_)
  · intro R' hm
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [hs_mc, Reg.x0, wp_norm, arm64_norm, *]
    · simp only [hs_mc, Reg.x1, wp_norm, arm64_norm, *]
    · simp only [hs_mc, Reg.x2, hes_len, wp_norm, arm64_norm, *]
    · exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
  · dsimp only [framelessMemcpyAcpSpec]
    refine sepWPp_pure_left_eq
      (φ := sf_mc.readReg64 .x0 = sf1.readReg64 .x0 ∧ AllocCallPreserved s_mc sf_mc ∧ VmPreserved s_mc sf_mc)
      (((sf1.readReg64 .x0) ↦ₛ x.st.es) ∗ (esPtr ↦ₛ x.st.es) ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        A.live (sf1.readReg64 .x0) 2080 1 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s_mc ∗ F_frame)
      (by sep_ac_rfl) ?_
    rintro ⟨_, hacp_mc, hvm_mc⟩
    rw [← A.pool_of_vmPreserved hvm_mc]
    rcases hcs_mc with ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m,
      hx27_m, hx28_m, hfp_m, hvregs_m⟩
    simp only [hs_mc, wp_norm, arm64_norm] at hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
    simp only [hs_mc, wp_norm, arm64_norm] at hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    have htr_mc : sf_mc.trace = s0.trace := by
      have ht := hacp_mc.2.1
      simpa only [hs_mc, wp_norm, arm64_norm, htr1'] using ht
    have hsp_sf_mc : sf_mc.sp = s0.sp - 336#64 := hsp_mc_rel.trans hsp_mc
    have hsp_sf_mc_norm : sf_mc.readReg64 .sp = s0.sp - 336#64 := hsp_sf_mc
    simp only [wp_norm, arm64_norm] at hsp_sf_mc_norm
    wp_steps_sync_pool ((blkPl_347).base + 516#64)
    simp only [State.setMem_setMem]
    refine sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hcont _ (sf1.readReg64 .x0) hne1
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [State.sp, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hvregs_m, hvregs_1, hvregs_s, hvregs])
        (by simp only [Reg.x8, wp_norm, arm64_norm, *])
        (by simp only [Reg.x19, wp_norm, arm64_norm, *])
        (by simp only [Reg.x20, wp_norm, arm64_norm, *])
        (by simp only [Reg.x22, Reg.x0, wp_norm, arm64_norm, *])
        (by simp only [Reg.x23, wp_norm, arm64_norm, *])
        (by simp only [Reg.x24, wp_norm, arm64_norm, *])
        (by simp only [Reg.x25, wp_norm, arm64_norm, *])
        (by simp only [Reg.x26, wp_norm, arm64_norm, *])
        (by simp only [Reg.x27, wp_norm, arm64_norm, *])
        (by simp only [Reg.x28, wp_norm, arm64_norm, *])
        (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

/-- Fixed-base budget-threaded 2080-byte workspace allocation and `memcpy` (`+472 → +516`) on
    `tripleRatchetProgAtExt b ext` under `AllocContracts4K b A lim ext`. -/
theorem send_ct2_5d8_to_604_wpp {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hFit : FitsEvents M lim stCost (rustAllocEvents 2080 1))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 472#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      esWorkPtr ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 516#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x8 = 0#64 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = 2080#64 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ x.st.es) ∗
          A.live esWorkPtr 2080 1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp := by
  have hshim := shim_ok_at_sendCt2 hA
  have hallocNoOom := allocNoOom_ok_at_sendCt2 hA
  have hmemcpy := memcpy_ok_at_sendCt2 hA
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19
  clear hA
  send_ct2_fetches_range b trapHooks 472 44
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
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_shim hs_shim => ?_
  rw [← hs_shim]
  have hsp_shim : s_shim.sp = s0.sp - 336#64 := by
    simp only [hs_shim, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_noPanic hshim ()
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_shim ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by rw [hs_shim]; wp_norm_goal)
    (by simp only [hs_shim, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_shim]; exact hfsp_align)
    (ret_pc := fnBase + 476#64)
    (by simp only [hs_shim, Reg.lr, wp_norm, arm64_norm, *])
    (fun R' hm => by
      dsimp only [withVmPreserved, sessionShimSpec]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by simp only [emp_sepConj]; sep_ac_rfl)) hm)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_shim hpc_shim hrun_shim hsp_shim_rel hcs_shim => ?_)
  dsimp only [withVmPreserved, sessionShimSpec]
  refine sepWPp_pure_left_eq (φ := VmPreserved s_shim sf_shim)
    (⌜sf_shim.trace = s_shim.trace⌝ ∗
      (esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_shim ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by sep_ac_rfl) ?_
  intro hvm_shim
  refine sepWPp_pure_left_eq (φ := sf_shim.trace = s_shim.trace)
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_shim ∗
      stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
    (by sep_ac_rfl) ?_
  intro htr_shim_raw
  rw [← A.pool_of_vmPreserved hvm_shim]
  rcases hcs_shim with ⟨hx19_s, hx20_s, hx21_s, hx22_s, hx23_s, hx24_s, hx25_s, hx26_s,
    hx27_s, hx28_s, hfp_s, hvregs_s⟩
  simp only [hs_shim, wp_norm, arm64_norm] at hx19_s hx20_s hx21_s hx22_s hx23_s hx24_s
  simp only [hs_shim, wp_norm, arm64_norm] at hx25_s hx26_s hx27_s hx28_s hfp_s hvregs_s
  have htr_shim : sf_shim.trace = s0.trace := by
    simpa only [hs_shim, wp_norm, arm64_norm, htr] using htr_shim_raw
  have hsp_sf_shim : sf_shim.sp = s0.sp - 336#64 := hsp_shim_rel.trans hsp_shim
  have hsp_sf_shim_norm : sf_shim.readReg64 .sp = s0.sp - 336#64 := hsp_sf_shim
  simp only [wp_norm, arm64_norm] at hsp_sf_shim_norm
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_alloc hs_alloc => ?_
  rw [← hs_alloc]
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine sepWPp_fold_eq
    ((esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s_alloc ∗ F_frame)
    hstack_alloc (by sep_ac_rfl) ?_
  have hlay_2080 : RustLayoutOk 2080 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine call_rustAllocNoOom_cs_wppBase hallocNoOom 2080 1 stCost hlay_2080 hFit
    (memRegion (s0.sp - 16720#64) 12288 ∗ (esPtr ↦ₛ x.st.es) ∗ F_frame)
    (ret_pc := fnBase + 488#64) (sp_call := s0.sp - 336#64)
    (by rw [hs_alloc]; wp_norm_goal)
    (by simp only [hs_alloc, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, State.sp, wp_norm, arm64_norm, *]) hfsp_align
    (by simp only [hs_alloc, Reg.lr, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x0, wp_norm, arm64_norm, *])
    (by simp only [hs_alloc, Reg.x1, wp_norm, arm64_norm, *])
    (by sep_ac_rfl)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 hacp1 hne1 _ => ?_)
  have htr1 : sf1.trace = s_alloc.trace := hacp1.2.1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
    hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [hs_alloc, wp_norm, arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
  simp only [hs_alloc, wp_norm, arm64_norm] at hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1 htr1
  have htr1' : sf1.trace = s0.trace := htr1.trans htr_shim
  have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hne1
  have hsp1_norm : sf1.readReg64 .sp = s0.sp - 336#64 := hsp1
  simp only [wp_norm, arm64_norm] at hsp1_norm
  have hstack_back :
      memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
        stackAt (s0.sp - 336#64) extHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
  refine sepWPp_fold_eq
    (A.live (sf1.readReg64 .x0) 2080 1 ∗
      memRegion (sf1.readReg64 .x0) 2080 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) sf1 ∗
      (esPtr ↦ₛ x.st.es) ∗ F_frame)
    hstack_back (by sep_ac_rfl) ?_
  have hmr_es :
      memRegion (sf1.readReg64 .x0) 2080 ⊢
        memRegion (sf1.readReg64 .x0) x.st.es.length := by
    rw [hes_len]; exact Entails.refl _
  refine sepWPp_fold_eq
    (stackAt (s0.sp - 336#64) extHookStack ∗
      A.live (sf1.readReg64 .x0) 2080 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) sf1 ∗
      (esPtr ↦ₛ x.st.es) ∗ F_frame)
    hmr_es (by sep_ac_rfl) ?_
  wp_steps_rebase_pool
    (fnBase + bv% (ls_off% "memcpy" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
  refine sepWPp_intro_state fun s_mc hs_mc => ?_
  rw [← hs_mc]
  have hsp_mc : s_mc.sp = s0.sp - 336#64 := by
    simp only [hs_mc, State.sp, wp_norm, arm64_norm, *]
  refine sepWPp_call_noPanic hmemcpy
    (sf1.readReg64 .x0, esPtr, x.st.es)
    (A.live (sf1.readReg64 .x0) 2080 1 ∗
      A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s_mc ∗ F_frame)
    (by rw [hs_mc]; wp_norm_goal)
    (by simp only [hs_mc, wp_norm, arm64_norm, *])
    (by rw [State.spAligned, hsp_mc]; exact hfsp_align)
    (ret_pc := fnBase + 512#64)
    (by simp only [hs_mc, Reg.lr, wp_norm, arm64_norm, *])
    ?_ (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (fun sf_mc hpc_mc hrun_mc hsp_mc_rel hcs_mc => ?_)
  · intro R' hm
    dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp_mc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [hs_mc, Reg.x0, wp_norm, arm64_norm, *]
    · simp only [hs_mc, Reg.x1, wp_norm, arm64_norm, *]
    · simp only [hs_mc, Reg.x2, hes_len, wp_norm, arm64_norm, *]
    · exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hm
  · dsimp only [withStack, withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hsp_mc]
    refine sepWPp_pure_left_eq (φ := VmPreserved s_mc sf_mc)
      (⌜sf_mc.readReg64 .x0 = sf1.readReg64 .x0 ∧ sf_mc.trace = s_mc.trace⌝ ∗
        ((sf1.readReg64 .x0) ↦ₛ x.st.es) ∗ (esPtr ↦ₛ x.st.es) ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        A.live (sf1.readReg64 .x0) 2080 1 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s_mc ∗ F_frame)
      (by sep_ac_rfl) ?_
    intro hvm_mc
    refine sepWPp_pure_left_eq (φ := sf_mc.readReg64 .x0 = sf1.readReg64 .x0 ∧ sf_mc.trace = s_mc.trace)
      (((sf1.readReg64 .x0) ↦ₛ x.st.es) ∗ (esPtr ↦ₛ x.st.es) ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        A.live (sf1.readReg64 .x0) 2080 1 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s_mc ∗ F_frame)
      (by sep_ac_rfl) ?_
    rintro ⟨_, htr_mc_raw⟩
    rw [← A.pool_of_vmPreserved hvm_mc]
    rcases hcs_mc with ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m,
      hx27_m, hx28_m, hfp_m, hvregs_m⟩
    simp only [hs_mc, wp_norm, arm64_norm] at hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m
    simp only [hs_mc, wp_norm, arm64_norm] at hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    have htr_mc : sf_mc.trace = s0.trace := by
      simpa only [hs_mc, wp_norm, arm64_norm, htr1'] using htr_mc_raw
    have hsp_sf_mc : sf_mc.sp = s0.sp - 336#64 := hsp_mc_rel.trans hsp_mc
    have hsp_sf_mc_norm : sf_mc.readReg64 .sp = s0.sp - 336#64 := hsp_sf_mc
    simp only [wp_norm, arm64_norm] at hsp_sf_mc_norm
    wp_steps_rebase_pool (fnBase + 516#64)
    refine sepWPp_rw_pre_eq (by sep_ac_rfl)
      (hcont _ (sf1.readReg64 .x0) hne1
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [State.sp, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, hvregs_m, hvregs_1, hvregs_s, hvregs])
        (by simp only [Reg.x8, wp_norm, arm64_norm, *])
        (by simp only [Reg.x19, wp_norm, arm64_norm, *])
        (by simp only [Reg.x20, wp_norm, arm64_norm, *])
        (by simp only [Reg.x22, Reg.x0, wp_norm, arm64_norm, *])
        (by simp only [Reg.x23, wp_norm, arm64_norm, *])
        (by simp only [Reg.x24, wp_norm, arm64_norm, *])
        (by simp only [Reg.x25, wp_norm, arm64_norm, *])
        (by simp only [Reg.x26, wp_norm, arm64_norm, *])
        (by simp only [Reg.x27, wp_norm, arm64_norm, *])
        (by simp only [Reg.x28, wp_norm, arm64_norm, *])
        (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

/-- Relocatable `[LibsignalPlacement]` budget-threaded Segment 2 (`+136 → +552`):
    scans `es[1536..2048)` for the libcrux issue-1275 halfword bound and conditionally allocates
    and byte-swaps a 2080-byte workspace, updating `A.pool lim stCost` to
    `A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost)`. -/
theorem send_ct2_scan_to_628_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hFit : FitsEvents M lim stCost (sendCt2FlipAllocEvents x.st.es))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      st'.pc = (blkPl_347).base + 552#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp := by
  have hlen512 : ((x.st.es.drop 1536).take 512).length = 512 := by
    rw [List.length_take, List.length_drop, hes_len]; rfl
  have hbs_ne : (x.st.es.drop 1536).take 512 ≠ [] := by
    intro hnil; rw [hnil] at hlen512; contradiction
  have hbs_mod : ((x.st.es.drop 1536).take 512).length % 2 = 0 := by rw [hlen512]
  have hbs_le : ((x.st.es.drop 1536).take 512).length ≤ 512 := by omega
  have hrem_eq : (512#64 : BitVec 64) = BitVec.ofNat 64 ((x.st.es.drop 1536).take 512).length := by
    rw [hlen512]
  have hpre_split : ∀ (P_pool : SepProp),
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        P_pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
      (((esPtr + 1536#64) ↦ₛ ((x.st.es.drop 1536).take 512)) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        P_pool ∗
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
    intro P_pool
    rw [es_scan_split esPtr x.st.es hes_len]
    sep_ac_rfl
  by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
  · refine SepWPp.of_sepWP (mid := (blkPl_347).base + 552#64) ?_
    rw [hpre_split (A.pool lim stCost st)]
    refine SepWP.mono
      (scan_loop_false_placed_pool_ok A lim stCost
        (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28) ?_
    rintro sf Pf hpc_sf hrun_sf ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved, _⟩
    have hwork : (esPtr ↦ₛ x.st.es) ⊢ sendCt2EsWorkAt A.repAlloc esPtr esPtr x.st.es := by
      unfold sendCt2EsWorkAt
      simp only [hflip, Bool.false_eq_true, ↓reduceIte]
      exact Entails.pure_right trivial (Entails.refl _)
    have hevs_nil : sendCt2FlipAllocEvents x.st.es = [] := by
      unfold sendCt2FlipAllocEvents
      simp only [hflip, Bool.false_eq_true, ↓reduceIte]
    have hPf_back : Pf ⊢
        sendCt2EsWorkAt A.repAlloc esPtr esPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) sf ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf, ← hpre_split (A.pool lim stCost sf), hevs_nil, M.stepEvents_nil]
      exact sepConj_mono_left hwork
    refine sepWPp_weaken_pre hPf_back ?_
    exact hcont sf esPtr hpc_sf hrun_sf
      (hsaved.sp.trans hsp) (hsaved.trace.trans htr) (hsaved.vregs.trans hvregs)
      (hsaved.x19.trans hx19) hsaved.x20
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx21_sf])
      (hx22_sf.trans hx19)
      hsaved.x23 hsaved.x24 hsaved.x25 hsaved.x26 hsaved.x27
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx28_sf])
      hsaved.x29
  · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
      Bool.eq_true_of_not_eq_false hflip
    have hevs_alloc : sendCt2FlipAllocEvents x.st.es = rustAllocEvents 2080 1 := by
      unfold sendCt2FlipAllocEvents
      simp only [hflip_t, ↓reduceIte]
    have hFit2080 : FitsEvents M lim stCost (rustAllocEvents 2080 1) := by
      rwa [← hevs_alloc]
    refine SepWPp.of_sepWP (mid := (blkPl_347).base + 472#64) ?_
    rw [hpre_split (A.pool lim stCost st)]
    refine SepWP.mono
      (scan_loop_true_placed_pool_ok A lim stCost
        (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hbs_ne hbs_mod hbs_le hrem_eq hflip_t hpc hrun hx8 hx9 hx10 hx11 hx13) ?_
    rintro s5d8 P5d8 hpc_5d8 hrun_5d8 ⟨hP5d8, hsaved1, _⟩
    have hP5d8_eq : P5d8 =
        (esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s5d8 ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) := by
      rw [hP5d8, ← hpre_split (A.pool lim stCost s5d8)]
      sep_ac_rfl
    rw [hP5d8_eq]
    refine send_ct2_5d8_to_604_placed_wpp hshim halloc hmemcpy
      x stCost esPtr s0 s5d8 ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame)
      hFit2080 hes_len hpc_5d8 hrun_5d8
      (hsaved1.sp.trans hsp) hsp_s0 (hsaved1.trace.trans htr)
      (hsaved1.vregs.trans hvregs) (hsaved1.x19.trans hx19) ?_
    intro s604 esWorkPtr hwork_ne hpc604 hrun604 hsp604 htr604 hvregs604
      hx8_604 hx19_604 hx20_604 hx22_604 hx23_604 hx24_604 hx25_604 hx26_604
      hx27_604 hx28_604 hx29_604
    refine SepWPp.of_sepWP (mid := (blkPl_347).base + 552#64) ?_
    have h2048_len : (x.st.es.take 2048).length = 2048 := by
      rw [List.length_take, hes_len]; rfl
    have h2048_ne : x.st.es.take 2048 ≠ [] := by
      intro hnil; rw [hnil] at h2048_len; contradiction
    have h2048_mod : (x.st.es.take 2048).length % 2 = 0 := by rw [h2048_len]
    have h2048_sum : (0#64 : BitVec 64).toNat + (x.st.es.take 2048).length = 2048 := by
      rw [h2048_len]; rfl
    have hsplit_swap :
        (esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s604 ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ (x.st.es.take 2048)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s604 ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
      rw [es_swap_split esWorkPtr x.st.es hes_len]
      sep_ac_rfl
    rw [hsplit_swap]
    refine SepWP.mono
      (swap_loop_placed_pool_ok A lim (M.stepEvents (rustAllocEvents 2080 1) stCost)
        esWorkPtr (x.st.es.take 2048) 0#64 s604
        (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        h2048_ne h2048_mod h2048_sum hpc604 hrun604 hx22_604 hx8_604) ?_
    rintro st' Pf2 hpc' hrun' ⟨hPf2, hx21', hsaved2, _⟩
    have hwork :
        (esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1 ⊢
          sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es := by
      unfold sendCt2EsWorkAt
      simp only [hflip_t, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      exact Entails.pure_right hwork_ne (Entails.of_eq (by sep_ac_rfl))
    have hPf2_reord :
        ((esWorkPtr + 0#64) ↦ₛ CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs (x.st.es.take 2048)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ CryptoVerification.LibsignalSpqrV1.swapAdjacentPairs (x.st.es.take 2048)) ∗
          ((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      sep_ac_rfl
    have hpost_ent : Pf2 ⊢
        sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf2, hPf2_reord, es_swap_join esWorkPtr x.st.es hes_len, hevs_alloc]
      refine Entails.trans (Entails.of_eq (show _ =
        ((esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1) ∗
          ((lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hwork
    refine sepWPp_weaken_pre hpost_ent ?_
    exact hcont st' esWorkPtr hpc' hrun'
      (hsaved2.sp.trans hsp604) (hsaved2.trace.trans htr604) (hsaved2.vregs.trans hvregs604)
      (hsaved2.x19.trans hx19_604)
      ((hsaved2.x20.trans hx20_604).trans hsaved1.x20)
      (by simp only [hflip_t, ↓reduceIte, hx21'])
      (hsaved2.x22.trans hx22_604)
      ((hsaved2.x23.trans hx23_604).trans hsaved1.x23)
      ((hsaved2.x24.trans hx24_604).trans hsaved1.x24)
      ((hsaved2.x25.trans hx25_604).trans hsaved1.x25)
      ((hsaved2.x26.trans hx26_604).trans hsaved1.x26)
      ((hsaved2.x27.trans hx27_604).trans hsaved1.x27)
      (by simp only [hflip_t, ↓reduceIte, hsaved2.x28.trans hx28_604])
      ((hsaved2.x29.trans hx29_604).trans hsaved1.x29)

theorem send_ct2_scan_to_628_placed_preEnv_wpp [LibsignalPlacement] {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpyAcpSpec)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (blkPl_347).base + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      st'.pc = (blkPl_347).base + 552#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim st0 st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp :=
  send_ct2_scan_to_628_placed_wpp hshim halloc hmemcpy x st0 esPtr s0 st F_frame
    (fitsEvents_flipAlloc_of_preEnv hPre) hes_len hpc hrun hsp hsp_s0 htr hvregs
    hx8 hx9 hx10 hx11 hx13 hx19 hx28 hcont

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget
