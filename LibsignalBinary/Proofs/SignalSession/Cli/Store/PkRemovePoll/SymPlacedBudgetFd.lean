/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.SymPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.BranchesPlacedBudgetFd
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded Relocatable Symbolic Execution of `remove_pre_key::{closure#0}`

Proves `pkRemovePoll_placed_ok_fd` on Block `575` (`lsProg_575 H`) against
`withFdsGe3Closed (pkRemovePollSpecPlaced …)` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.SymPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv TraceFsSound sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli
  (DirGhost PkPollGhost ReadRule dirAt getResultAt keyName pkBoxAt subroutine_ok_withFsInv)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_575 blkPl_575)
open CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
  (calleeSavedVRegs_writeVReg128_0 extractLsb_0_64_append_p extractLsb_64_64_append_p
   files_eq_of_fsInv_trace_eq fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState
   fs_writeReg fs_writeReg32 fs_writeReg64 fs_writeVReg128 pkRemoveFrameSlots pollMinStk
   savedCalleeSlots sepWPp_conseq sepWPp_name_state_placed sepWPp_of_sepWP_final_placed
   sepWPp_with_stk_bound setWidth_32_setWidth_64 setWidth_64_append_p spAligned_sub_c0
   stackAt_pkRemove_eq stackAt_sub_split subMax subStack_split vecU8Tail vecU8_eq_bytes_tail)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced
   pkRemovePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv OptPkRemoveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudgetFd
  (pkrm_call_decimal_fs_placed_fd pkrm_call_dirGet_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.BranchesPlacedBudget
  (postGetCommon_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.BranchesPlacedBudgetFd
  (pkrm_branch_err_placed_fd pkrm_branch_ok_cons_placed_fd pkrm_branch_ok_nil_placed_fd)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0 setWidth_32_setWidth_64
  extractLsb_0_64_append_p extractLsb_64_64_append_p setWidth_64_append_p
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

/-- Top-level two-sided `withFdsGe3Closed` proof of `remove_pre_key::{closure#0}` (Block `575`)
against `withFdsGe3Closed (pkRemovePollSpecPlaced …)`. -/
theorem pkRemovePoll_placed_ok_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hDecimal : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hGet : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (hFs : TraceFsSound ((blkPC_575).rebase (blkPl_575).base H))
    (hstk : pollMinStk decStk getStk putStk ≤ stk) :
    subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (blkPl_575).base
      (withFdsGe3Closed
        (pkRemovePollSpecPlaced rd pathOk A lim
          (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_al0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_al0
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hGetFs := subroutine_ok_withFsInv hFs hGet s0.fs.files s0.trace
  let RemEnv := CliPkRemovePollEnv rd DecEnv GetEnv PutEnv
  let TopSpec := withFdsGe3Closed (pkRemovePollSpecPlaced rd pathOk A lim RemEnv stk)
  refine ⟨TopSpec.pre (x, st0) s0, R, hpre, ?_⟩
  generalize hQ_eq :
    (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ TopSpec.post (x, st0) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q
  generalize hQp_eq :
    (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ TopSpec.onPanic (x, st0) s0 sf ∗ R))
    = Qp
  have hbrErr := @pkrm_branch_err_placed_fd _ M A lim H rd pathOk DecEnv GetEnv PutEnv
    decStk getStk putStk stk hFsAlloc
  have hbrNil := @pkrm_branch_ok_nil_placed_fd _ M A lim H rd pathOk DecEnv GetEnv PutEnv
    decStk getStk putStk stk hFsAlloc
  have hbrCons := @pkrm_branch_ok_cons_placed_fd _ M A lim H rd pathOk DecEnv GetEnv PutEnv
    decStk getStk putStk stk Qp hFsAlloc hDecimal hPut
  clear hFs hDecimal hGet hPut hFsAlloc
  dsimp only [TopSpec, withFdsGe3Closed, pkRemovePollSpecPlaced, withLsCodeRoLoaded]
  refine SepWPp.pure_elim fun hfds0 => ?_
  rw [sepConj_comm]
  refine SepWPp.pure_elim fun hcrl0 => ?_
  refine SepWPp.pure_elim fun ⟨hx0_0, hx8_0, ⟨hname_lt, hdir_lt, hpOk⟩, hdchg, hfit0⟩ => ?_
  have hfit_dec1 : FitsEnv M lim st0 (DecEnv x.id) := hfit0.seq_left
  refine sepWPp_with_stk_bound (a := x.fut) (v := x.self)
    (Rest := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
      memRegion (x.fut + 0xd#64) 3 ∗ dirAt A.repAlloc x.self x.dir ∗
      memRegion x.out 48 ∗ A.pool lim st0 s0)
    (Entails.of_eq (by unfold pkBoxAt; sep_ac_rfl))
    fun hstk_hi => ?_
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdec_le : decStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hget_le : getStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  rw [stackAt_sub_split s0.sp hstk hstk_hi,
      stackAt_pkRemove_eq s0.sp hmin_hi,
      subStack_split s0.sp hdec_le hmin_hi]
  unfold pkBoxAt pkRemoveFrameSlots
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun q_sp0 =>
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => ?_
  apply sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl0
  wp_steps_sync_pool (lsmpl.base 597)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl1
  refine sepWPp_name_state_placed fun s1 hs1 => ?_
  have hs1_pc : s1.pc = lsmpl.base 597 := by
    rw [hs1]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs1_lr : s1.readReg64 Reg.lr = (blkPl_575).base + 68#64 := by
    rw [hs1]; simp only [wp_norm, arm64_norm, *]
  have hs1_run : s1.status = .Running := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_sp : s1.sp = s0.sp - 0xc0#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_tr : s1.trace = s0.trace := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_fs : s1.fs = s0.fs := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_fds : FdsGe3Closed s1.fs := hs1_fs ▸ hfds0
  have hs1_x0 : s1.readReg64 .x0 = s0.sp - 0x78#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x1 : s1.readReg32 .x1 = x.id := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x19 : s1.readReg64 .x19 = x.fut := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x20 : s1.readReg64 .x20 = x.out := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x22 : s1.readReg64 .x22 = x.self := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x23 : s1.readReg64 .x23 = BitVec.setWidth 64 x.id := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_x28 : s1.readReg64 .x28 = s0.readReg64 .x28 := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_fp : s1.readReg64 .x29 = s0.sp - 0x60#64 := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_vregs : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
    rw [hs1]; simp only [arm64_norm, *]
  rw [← hs1] at hcrl1 ⊢
  clear hs1
  let F_dec1 : SepProp :=
    pkBoxAt x.fut x.self x.id 0#8 ∗
    dirAt A.repAlloc x.self x.dir ∗
    memRegion x.out 48 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - decStk) ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xa8#64) 48 ∗
    savedCalleeSlots s0
  refine pkrm_call_decimal_fs_placed_fd hDecFs
    { n := x.id, ret := s0.sp - 0x78#64 } st0 F_dec1
    hs1_pc hs1_run (spAligned_sub_c0 hsp_align hs1_sp) hs1_lr hcrl1
    (by rw [← hs1_fs, ← hs1_tr]; exact FsInv.of_entry s1) hs1_fds
    hs1_x0 hs1_x1 hfit_dec1
    (Entails.of_eq (by
      rw [hs1_sp]
      unfold F_dec1 pkBoxAt savedCalleeSlots
      dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.lr]
      sep_ac_rfl))
    fun sm1 evs1 hpcm1 hrunm1 hspm1 hcsm1 hcrlm1 hfsm1 hfds_m1 htrm1 hevs1 => ?_
  rw [hs1_sp]
  let st1 := M.stepEvents evs1 st0
  have hfit_after_dec1 : FitsEnv M lim st1
      (SeqEnv (GetEnv s0.fs.files x.dir (keyName x.id))
        (OptPkRemoveTailEnv DecEnv PutEnv x (x.dir.get rd s0.fs.files (keyName x.id)))) :=
    hfit0.seq_right hevs1
  rcases hcsm1 with
    ⟨hx19_1, hx20_1, _, hx22_1, hx23_1, _, _, _, _, hx28_1, hfp_1, hvregs_1⟩
  have hsp_m1 : sm1.sp = s0.sp - 0xc0#64 := hspm1.trans hs1_sp
  have hsp_al1 : sm1.spAligned = true := spAligned_sub_c0 hsp_align hsp_m1
  have hx19_m1 : sm1.readReg64 .x19 = x.fut := hx19_1.trans hs1_x19
  have hx20_m1 : sm1.readReg64 .x20 = x.out := hx20_1.trans hs1_x20
  have hx22_m1 : sm1.readReg64 .x22 = x.self := hx22_1.trans hs1_x22
  have hx23_m1 : sm1.readReg64 .x23 = BitVec.setWidth 64 x.id := hx23_1.trans hs1_x23
  have hx28_m1 : sm1.readReg64 .x28 = s0.readReg64 .x28 := hx28_1.trans hs1_x28
  have hfp_m1 : sm1.readReg64 .x29 = s0.sp - 0x60#64 := hfp_1.trans hs1_fp
  have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := hvregs_1.trans hs1_vregs
  have htr_m1 : sm1.trace = s0.trace := htrm1.trans hs1_tr
  have hfiles_m1 : sm1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfsm1 htr_m1
  let nameBs := keyName x.id
  have hrestk1 :
      stackAt (s0.sp - 0xc0#64) decStk ∗
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk) =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - getStk) ∗
      stackAt (s0.sp - 0xc0#64) getStk := by
    rw [sepConj_comm, ← subStack_split s0.sp hdec_le hmin_hi,
        subStack_split s0.sp hget_le hmin_hi]
  unfold F_dec1
  change SepWPp _ _ _
    ((vecU8 A.repAlloc (s0.sp - 0x78#64) nameBs ∗ stackAt (s0.sp - 0xc0#64) decStk ∗
      A.pool lim st1 sm1) ∗ _) _ _
  rw [vecU8_eq_bytes_tail A.repAlloc (s0.sp - 0x78#64) nameBs (s0.sp - 0x70#64) (s0.sp - 0x68#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun nameCap => SepWPp.exists_elim fun namePtr =>
    SepWPp.pure_elim fun ⟨hnlen, hnlt, hnptr⟩ => ?_
  refine sepWPp_conseq
    (P' := ((stackAt (s0.sp - 0xc0#64) decStk ∗
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk)) ∗
      ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
      ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
      ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      A.pool lim st1 sm1 ∗
      pkBoxAt x.fut x.self x.id 0#8 ∗
      dirAt A.repAlloc x.self x.dir ∗
      memRegion x.out 48 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
      memRegion (s0.sp - 0xb0#64) 8 ∗
      memRegion (s0.sp - 0xa8#64) 48 ∗
      savedCalleeSlots s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  rw [hrestk1]
  simp only [sepConj_assoc]
  apply sepWPp_seq_lscro (mid := lsmpl.base 589) hcrlm1
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl2
  have hx3_len : (BitVec.ofNat 64 nameBs.length).toNat = nameBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_name_state_placed fun s2 hs2 => ?_
  have hs2_pc : s2.pc = lsmpl.base 589 := by
    rw [hs2]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs2_lr : s2.readReg64 Reg.lr = (blkPl_575).base + 88#64 := by
    rw [hs2]; simp only [wp_norm, arm64_norm, *]
  have hs2_run : s2.status = .Running := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_sp : s2.sp = s0.sp - 0xc0#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_tr : s2.trace = s0.trace := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_fs : s2.fs = sm1.fs := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_files : s2.fs.files = s0.fs.files := by rw [hs2_fs]; exact hfiles_m1
  have hs2_fds : FdsGe3Closed s2.fs := hs2_fs ▸ hfds_m1
  have hs2_x0 : s2.readReg64 .x0 = s0.sp - 0xa8#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x1 : s2.readReg64 .x1 = x.self := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x2 : s2.readReg64 .x2 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x3 : (s2.readReg64 .x3).toNat = nameBs.length := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_x19 : s2.readReg64 .x19 = x.fut := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x20 : s2.readReg64 .x20 = x.out := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x21 : s2.readReg64 .x21 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x22 : s2.readReg64 .x22 = x.self := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x23 : s2.readReg64 .x23 = BitVec.setWidth 64 x.id := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_x28 : s2.readReg64 .x28 = s0.readReg64 .x28 := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_fp : s2.readReg64 .x29 = s0.sp - 0x60#64 := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_vregs : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
    rw [hs2]; simp only [arm64_norm, *]
  rw [← hs2] at hcrl2 ⊢
  clear hs2
  have hfit_get : FitsEnv M lim st1 (GetEnv s2.fs.files x.dir nameBs) := by
    simpa only [hs2_files, nameBs] using hfit_after_dec1.seq_left
  let F_get : SepProp :=
    ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - getStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8
  refine pkrm_call_dirGet_placed_fd hGetFs
    { ret := s0.sp - 0xa8#64, self := x.self, dir := x.dir,
      nameA := namePtr, name := nameBs, nameRo := false } st1 F_get
    hs2_pc hs2_run (spAligned_sub_c0 hsp_align hs2_sp) hs2_lr hcrl2
    (by rw [← hs2_files, ← hs2_tr]; exact FsInv.of_entry s2) hs2_fds
    hs2_x0 hs2_x1 hs2_x2 hs2_x3
    hname_lt hdir_lt hpOk hfit_get
    (Entails.of_eq (by rw [hs2_sp]; unfold F_get; dsimp only; sep_ac_rfl))
    fun sm2 evs2 gr hpcm2 hrunm2 hspm2 hcsm2 hcrlm2 _hfsm2 hfds_m2 hgr => ?_
  rw [hs2_sp]
  rcases hcsm2 with
    ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, _, _, hx28_2, hfp_2, hvregs_2⟩
  have hsp_m2 : sm2.sp = s0.sp - 0xc0#64 := hspm2.trans hs2_sp
  have hx19_m2 : sm2.readReg64 .x19 = x.fut := hx19_2.trans hs2_x19
  have hx20_m2 : sm2.readReg64 .x20 = x.out := hx20_2.trans hs2_x20
  have hx21_m2 : sm2.readReg64 .x21 = namePtr := hx21_2.trans hs2_x21
  have hx22_m2 : sm2.readReg64 .x22 = x.self := hx22_2.trans hs2_x22
  have hx23_m2 : sm2.readReg64 .x23 = BitVec.setWidth 64 x.id := hx23_2.trans hs2_x23
  have hx28_m2 : sm2.readReg64 .x28 = s0.readReg64 .x28 := hx28_2.trans hs2_x28
  have hfp_m2 : sm2.readReg64 .x29 = s0.sp - 0x60#64 := hfp_2.trans hs2_fp
  have hvregs_m2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := hvregs_2.trans hs2_vregs
  have hgr0 : gr = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace :=
    ⟨by simpa only [nameBs, hs2_files] using hgr.1, hgr.2.1.trans hs2_tr⟩
  have hevs2 : GetEnv s0.fs.files x.dir (keyName x.id) evs2 := by
    simpa only [nameBs, hs2_files] using hgr.2.2
  let st2 := M.stepEvents evs2 st1
  have hfit_tail : FitsEnv M lim st2 (OptPkRemoveTailEnv DecEnv PutEnv x gr) := by
    rw [hgr0.1]
    exact hfit_after_dec1.seq_right hevs2
  clear hs2_fs hs2_files hgr
  have hpost_get :
      ((getResultAt A.repAlloc (s0.sp - 0xa8#64) gr ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt false namePtr nameBs ∗
        stackAt (s0.sp - 0xc0#64) getStk ∗ A.pool lim st2 sm2) ∗ F_get) ⊢
      getResultAt A.repAlloc (s0.sp - 0xa8#64) gr ∗
        postGetCommon_placed A lim st2 s0 sm2 x decStk getStk putStk stk
          nameCap namePtr nameBs q_sp0 := by
    have hstk_merge :
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - getStk) ∗
        stackAt (s0.sp - 0xc0#64) getStk =
        stackAt (s0.sp - 0xc0#64) (subMax decStk getStk putStk) :=
      (subStack_split s0.sp hget_le hmin_hi).symm
    unfold F_get postGetCommon_placed
    have hpull :
        ((getResultAt A.repAlloc (s0.sp - 0xa8#64) gr ∗ dirAt A.repAlloc x.self x.dir ∗
          bytesAt false namePtr nameBs ∗
          stackAt (s0.sp - 0xc0#64) getStk ∗ A.pool lim st2 sm2) ∗
          ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
          vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - getStk) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          memRegion x.out 48 ∗
          pkBoxAt x.fut x.self x.id 0#8) =
        ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - getStk) ∗
          stackAt (s0.sp - 0xc0#64) getStk) ∗
          (getResultAt A.repAlloc (s0.sp - 0xa8#64) gr ∗
            ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
            bytesAt false namePtr nameBs ∗
            vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
            ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
            memRegion (s0.sp - 0xb0#64) 8 ∗
            savedCalleeSlots s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
            memRegion x.out 48 ∗
            pkBoxAt x.fut x.self x.id 0#8 ∗
            dirAt A.repAlloc x.self x.dir ∗
            A.pool lim st2 sm2)) := by
      sep_ac_rfl
    rw [hpull, hstk_merge]
    exact Entails.of_eq (by sep_ac_rfl)
  refine sepWPp_conseq hpost_get ?_
  subst hQ_eq hQp_eq
  dsimp only [TopSpec]
  rcases gr with ⟨⟩ | ⟨_ | ⟨b0, bsRest⟩⟩
  · apply sepWPp_of_sepWP_final_placed
    exact hbrErr x st0 evs1 evs2 R s0 sm2 nameCap namePtr nameBs q_sp0
      hstk hstk_hi hnlen hnlt hnptr hevs1 hevs2 hfds_m2 hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hcrlm2 hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2
  · apply sepWPp_of_sepWP_final_placed
    exact hbrNil x st0 evs1 evs2 R s0 sm2 nameCap namePtr nameBs q_sp0
      hstk hstk_hi hnlen hnlt hnptr hevs1 hevs2 hfds_m2 hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hcrlm2 hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2
  · exact hbrCons x st0 evs1 evs2 R s0 sm2 b0 bsRest nameCap namePtr nameBs q_sp0
      hstk hstk_hi hdchg hnlen hnlt hnptr hevs1 hevs2 hfit_tail hfds_m2 hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hfp_m2 hcrlm2
      hx28_m2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx22_m2 hx23_m2

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.SymPlacedBudgetFd
