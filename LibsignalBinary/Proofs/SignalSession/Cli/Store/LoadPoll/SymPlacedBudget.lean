/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.BranchesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.SymPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Relocatable `Ok(b :: bs)` Branch & Top-Level `load_session::{closure#0}`

Proves budget-threaded `lpoll_deser_copy_78_placed`, `lpoll_branch_ok_cons_placed`, and
`sessLoadPoll_placed_ok` on Block `569` (`lsProg_569 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.SymPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost okTagVec protocolAddressAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded TraceFsSound sepWP_seq_lscro sepWPp_seq_lscro
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
  (RecordTailInline recordCurCap recordHeap)
open CryptoVerification.E2E.Record
  (RecordGhost encodeRecord recDeserializeStack sessionRecordAt)
open CryptoVerification.E2E.InMem.SessionStoreImpl (ofRecordGhost)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule SessFileWf SessLoadAns SessLoadPollGhost addressText dirAt
   getResultAt pathOf sessLoadBoxAt subroutine_ok_withFsInv)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_569 blkPl_569)
open CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
  (calleeSavedVRegs_writeVReg128_0 epilogueOut epiloguePre extractLsb_0_64_append
   extractLsb_64_64_append files_eq_of_fsInv_trace_eq finish_common_reassemble
   fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState fs_writeReg
   fs_writeReg32 fs_writeReg64 fs_writeVReg128 getResultAt_ok_unpack loadPollFrameSlots
   okTagVec_add_two_eq_zero pollMinStk postGetCommon record_reassemble_for_poll
   record_unpack_for_poll savedCalleeSlots sepWPp_conseq sepWPp_name_state
   sepWPp_of_sepWP_final sepWPp_with_stk_bound setWidth_64_append slot170_ok_collapse
   slot170_split48 spAligned_sub_350 stackAt_loadPoll_eq stackAt_sub_split subMax
   subStack_split vecU8Tail vecU8_eq_bytes_tail vecU8_free_zero)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced addrTextSpecPlaced dirGetSpecPlaced sessDeserializeSpecPlaced
   sessLoadPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
  (CliLoadPollEnv OptLoadDeserEnv freeOnlyEvs_optDeallocBufEvents freeOnlyEvs_rustDeallocEvents
   lpoll_call_addrText_placed lpoll_call_deser_placed lpoll_call_dirGet_placed
   lpoll_memcpy_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.EpiloguePlacedBudget
  (lpoll_drop_bytes_13c_placed lpoll_finish_14c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.BranchesPlacedBudget
  (finish_common_reassemble_budget lpoll_branch_err_placed lpoll_branch_ok_nil_placed
   lpoll_post_entails_placed postGetCommon_atState)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0
  extractLsb_0_64_append extractLsb_64_64_append setWidth_64_append
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

private theorem state_setMem_setMem (st : State) (m1 m2 : Memory) :
    (st.setMem m1).setMem m2 = st.setMem m2 := by
  cases st
  rfl

/-- Post-`deserialize` copy block (`+0x078 .. +0x0b4`) on Block `569`, syncing `A.pool lim st`. -/
theorem lpoll_deser_copy_78_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (st : M.σ) (s0 s : State)
    (prevCap prevPtr curCap w4 w5 w6 c_sp0 : BitVec 64)
    (q140 : BitVec 128) (tail : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    {ret : BitVec 64}
    (hprev_lt : prevCap.toNat < 2 ^ 63)
    (htail_len : tail.length = 312)
    (hpc : s.pc = (blkPl_569).base + 120#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0x350#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx25 : s.readReg64 .x25 = s0.sp - 0x210#64)
    (hfoc : P ⊢
      ((s0.sp - 0x1e0#64) ↦₆₄ prevCap) ∗
      ((s0.sp - 0x1d8#64) ↦₆₄ prevPtr) ∗
      ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 0x1c8#64) ↦₆₄ curCap) ∗
      ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
      ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
      ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
      ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
      memRegion (s0.sp - 0x348#64) 312 ∗
      ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
      stackAt (s0.sp - 0x350#64) extHookStack ∗
      A.pool lim st s ∗
      F)
    (hk : ∀ (sm : State),
      sm.pc = (blkPl_569).base + 180#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 0x350#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x27 = prevCap →
      sm.readReg64 .x26 = prevPtr →
      sm.readReg64 .x25 = curCap →
      sm.readReg64 .x22 = w4 →
      sm.readReg64 .x28 = s0.sp - 0x210#64 →
      SepWP ((blkPC_569).rebase (blkPl_569).base H) ret sm
        ((((s0.sp - 0x348#64) ↦ₛ tail) ∗
          ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
          stackAt (s0.sp - 0x350#64) extHookStack) ∗
          (((s0.sp - 0x1e0#64) ↦₆₄ prevCap) ∗
            ((s0.sp - 0x1d8#64) ↦₆₄ prevPtr) ∗
            ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0x1c8#64) ↦₆₄ curCap) ∗
            ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
            ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
            ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0x210#64) ↦₁₂₈ (w6 ++ w5)) ∗
            A.pool lim st sm ∗
            F))
        post) :
    SepWP ((blkPC_569).rebase (blkPl_569).base H) ret s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hprev_beq : (prevCap + 1#64 == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have h1 := congrArg BitVec.toNat heq
    have hlt64 : prevCap.toNat + 1 < 2 ^ 64 := by omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at h1
    exact Nat.succ_ne_zero _ h1
  refine SepWP.weaken_pre hfoc ?_
  unfold Arm64.pointsTo128
  simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
  apply sepWP_seq_lscro (mid := lsρ memcpyName) hcrl
  let _ := hprev_beq
  wp_steps_sync_pool (lsρ memcpyName)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_mc
  try rw [state_setMem_setMem] at hcrl_mc ⊢
  apply sepWP_seq_lscro (mid := (blkPl_569).base + 180#64) hcrl_mc
  wp_call_lscro (lpoll_memcpy_placed_ok hC) hcrl_mc (s0.sp - 0x348#64, s0.sp - 0x1a8#64, tail)
  refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_b4
  refine SepWP.weaken_pre
    (Entails.of_eq (by
      have h440 : s0.sp - 0x1b8#64 + 8#64 = s0.sp - 432#64 := by bv_omega
      have h528 : s0.sp - 0x210#64 + 8#64 = s0.sp - 520#64 := by bv_omega
      unfold Arm64.pointsTo128
      simp only [hsp, h440, h528, extractLsb_0_64_append, extractLsb_64_64_append]
      sep_ac_rfl))
    (hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) hcrl_b4 (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]))

/-- Branch 3 (`+0x054` on `gr = .ok (b0 :: bsRest)`) on Block `569`, budget-threaded. -/
theorem lpoll_branch_ok_cons_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {LoadEnv : FsFiles → SessLoadPollGhost → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDeser : subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (x : SessLoadPollGhost) (st0 st2 : M.σ) (R : SepProp) (s0 sm2 : State)
    (r : SessionRecord (List (BitVec 8))) (b0 : BitVec 8) (bsRest : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (hstk : pollMinStk addrStk getStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (henc : encodeRecord r = b0 :: bsRest)
    (hsc : Scope r)
    (hgr : Except.ok (b0 :: bsRest) =
        x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
      sm2.trace = s0.trace)
    (hfit_des : FitsEnv M lim st2 (DeserEnv r))
    (hevs_fin : ∀ evs_des evs_free, DeserEnv r evs_des → FreeOnlyEvs evs_free →
      ∃ evs, LoadEnv s0.fs.files x evs ∧
        M.stepEvents evs_free (M.stepEvents evs_des st2) = M.stepEvents evs st0)
    (hpc : sm2.pc = (blkPl_569).base + 84#64)
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0x350#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.call.fut)
    (hx20 : sm2.readReg64 .x20 = x.call.out)
    (hx21 : sm2.readReg64 .x21 = namePtr)
    (hx25 : sm2.readReg64 .x25 = s0.sp - 0x210#64) :
    SepWPp ((blkPC_569).rebase (blkPl_569).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A.repAlloc (s0.sp - 0x1e0#64) (.ok (b0 :: bsRest)) ∗
        postGetCommon (A.atState lim st2 sm2) s0 x addrStk getStk stk
          nameCap namePtr nameBs c_sp0 q140)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (sessLoadPollSpecPlaced rd pathOk Scope A lim LoadEnv stk).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (sessLoadPollSpecPlaced rd pathOk Scope A lim LoadEnv stk).onPanic (x, st0) s0 sf ∗ R)) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdes_le : recDeserializeStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hext_le : extHookStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hdc78 := @lpoll_deser_copy_78_placed _ M A lim H hC
  have hf14c := lpoll_finish_14c_placed hC
  have hdb13c := lpoll_drop_bytes_13c_placed hC
  clear hC
  rw [← henc, postGetCommon_atState]
  rw [getResultAt_ok_unpack A.repAlloc s0.sp (encodeRecord r),
      subStack_split s0.sp hdes_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => SepWPp.exists_elim fun bytesPtr =>
    SepWPp.pure_elim fun ⟨hblen, hblt, hbptr⟩ => ?_
  have hlen_beq : (BitVec.ofNat 64 (b0 :: bsRest).length == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have h1 := congrArg BitVec.toNat heq
    have h2 : bsRest.length + 1 < 2 ^ 64 := by
      have : (b0 :: bsRest).length = bsRest.length + 1 := rfl
      rw [← this, ← henc]; omega
    simp only [List.length_cons, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at h1
    exact Nat.succ_ne_zero _ h1
  have hlen_beq' : (BitVec.ofNat 64 (encodeRecord r).length == 0#64) = false := by
    simpa only [henc] using hlen_beq
  apply sepWPp_seq_lscro (mid := lsmpl.base 46) hcrl
  let _ := hlen_beq; let _ := hlen_beq'
  wp_steps_sync_pool (lsmpl.base 46)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_ds
  try rw [state_setMem_setMem] at hcrl_ds ⊢
  refine sepWPp_name_state fun s3 hs3 => ?_
  have hs3_pc : s3.pc = lsmpl.base 46 := by
    rw [hs3]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs3_lr : s3.readReg64 Reg.lr = (blkPl_569).base + 120#64 := by
    rw [hs3]; simp only [wp_norm, arm64_norm, *]
  have hs3_run : s3.status = .Running := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_sp : s3.sp = s0.sp - 0x350#64 := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_tr : s3.trace = s0.trace := by rw [hs3]; simp only [hgr.2, arm64_norm, *]
  have hs3_x0 : s3.readReg64 .x0 = bytesPtr := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x1 : s3.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord r).length := by
    rw [hs3]; simp only [arm64_norm, *]
  have hs3_x8 : s3.readReg64 .x8 = s0.sp - 0x1e0#64 := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x19 : s3.readReg64 .x19 = x.call.fut := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x20 : s3.readReg64 .x20 = x.call.out := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x21 : s3.readReg64 .x21 = namePtr := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x23 : s3.readReg64 .x23 = bytesCap := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x24 : s3.readReg64 .x24 = bytesPtr := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x25 : s3.readReg64 .x25 = s0.sp - 0x210#64 := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_vregs : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hs3]; simp only [arm64_norm, *]
  rw [← hs3] at hcrl_ds ⊢
  clear hs3
  let F_des : SepProp :=
    vecU8Tail A.repAlloc bytesCap bytesPtr (encodeRecord r) ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    bytesAt false namePtr nameBs ∗
    vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x348#64) 312 ∗
    ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - recDeserializeStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion x.call.out 368 ∗
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    dirAt A.repAlloc x.self x.dir ∗
    protocolAddressAt A.repAlloc x.call.addr x.call.addrA
  refine lpoll_call_deser_placed hDeser
    { p := bytesPtr, out := s0.sp - 0x1e0#64, r := r } st2 F_des
    hs3_pc hs3_run (spAligned_sub_350 hsp_align hs3_sp) hs3_lr hcrl_ds
    hs3_x0 hs3_x1 hs3_x8 hsc hfit_des
    (by
      rw [hs3_sp]
      refine Entails.trans (Q :=
        (((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗
          ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (encodeRecord r).length) ∗
          memRegion (s0.sp - 0x1c0#64) 16 ∗ memRegion (s0.sp - 0x1b0#64) 320) ∗
        ((bytesPtr ↦ₛ encodeRecord r) ∗ A.pool lim st2 s3 ∗
          stackAt (s0.sp - 0x350#64) recDeserializeStack ∗ F_des))
        (Entails.of_eq (by
          unfold F_des CryptoVerification.SpqrV1.ChainProofs.bytesAt
          simp only [Bool.false_eq_true, ite_false]
          sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left (slot170_ok_collapse s0.sp okTagVec bytesCap bytesPtr
        (BitVec.ofNat 64 (encodeRecord r).length))) ?_
      exact Entails.of_eq (by sep_ac_rfl))
    fun sm3 evs_des gE2E hpcm3 hrunm3 hspm3 hcsm3 hcrlm3 htrm3 hevs_des _hcan => ?_
  rw [hs3_sp]
  let st3 : M.σ := M.stepEvents evs_des st2
  rcases hcsm3 with ⟨hx19_3, hx20_3, hx21_3, _, hx23_3, hx24_3, hx25_3, _, _, _, _, hvregs_3⟩
  have hx19_m3 : sm3.readReg64 .x19 = x.call.fut := hx19_3.trans hs3_x19
  have hx20_m3 : sm3.readReg64 .x20 = x.call.out := hx20_3.trans hs3_x20
  have hx21_m3 : sm3.readReg64 .x21 = namePtr := hx21_3.trans hs3_x21
  have hx23_m3 : sm3.readReg64 .x23 = bytesCap := hx23_3.trans hs3_x23
  have hx24_m3 : sm3.readReg64 .x24 = bytesPtr := hx24_3.trans hs3_x24
  have hx25_m3 : sm3.readReg64 .x25 = s0.sp - 0x210#64 := hx25_3.trans hs3_x25
  have hvregs_m3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := hvregs_3.trans hs3_vregs
  have htr_m3 : sm3.trace = s0.trace := htrm3.trans hs3_tr
  apply sepWPp_of_sepWP_final
  let g := ofRecordGhost gE2E
  have hunpack : sessionRecordAt A.repAlloc (s0.sp - 0x1e0#64) gE2E r ⊢
      (∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜g.prevCap.toNat < 2 ^ 63 ∧ RecordTailInline g r w4 w5 w6 tail⌝ ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ recordCurCap g) ∗
        ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
        ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
        ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
        recordHeap A.repAlloc g r) :=
    record_unpack_for_poll A.repAlloc s0.sp gE2E r
  unfold F_des
  have hrestk :
      stackAt (s0.sp - 0x350#64) recDeserializeStack ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - recDeserializeStack) =
      memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
        (subMax addrStk getStk - extHookStack) ∗
      stackAt (s0.sp - 0x350#64) extHookStack := by
    rw [sepConj_comm, ← subStack_split s0.sp hdes_le hmin_hi,
        subStack_split s0.sp hext_le hmin_hi]
  refine SepWP.weaken_pre
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hunpack))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun w4 => SepWP.exists_elim fun w5 =>
    SepWP.exists_elim fun w6 => SepWP.exists_elim fun tail => ?_
  refine SepWP.weaken_pre
    (Entails.of_eq (by
      unfold CryptoVerification.SpqrV1.ChainProofs.bytesAt
      simp only [Bool.false_eq_true, ite_false]
      sep_ac_rfl) :
      _ ⊢
      ⌜g.prevCap.toNat < 2 ^ 63 ∧ RecordTailInline g r w4 w5 w6 tail⌝ ∗
        (stackAt (s0.sp - 0x350#64) recDeserializeStack ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - recDeserializeStack)) ∗
        bytesAt false bytesPtr (encodeRecord r) ∗
        vecU8Tail A.repAlloc bytesCap bytesPtr (encodeRecord r) ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ recordCurCap g) ∗
        ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
        ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
        ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
        recordHeap A.repAlloc g r ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        bytesAt false namePtr nameBs ∗
        vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        memRegion (s0.sp - 0x348#64) 312 ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A.repAlloc x.self x.dir ∗
        protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
        A.pool lim st3 sm3) ?_
  refine SepWP.pure_elim fun ⟨hprev_lt, hinl⟩ => ?_
  rw [hrestk]
  have htail_len : tail.length = 312 := hinl.1
  let F_copy : SepProp :=
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - extHookStack) ∗
    bytesAt false bytesPtr (encodeRecord r) ∗
    vecU8Tail A.repAlloc bytesCap bytesPtr (encodeRecord r) ∗
    recordHeap A.repAlloc g r ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    bytesAt false namePtr nameBs ∗
    vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion x.call.out 368 ∗
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    dirAt A.repAlloc x.self x.dir ∗
    protocolAddressAt A.repAlloc x.call.addr x.call.addrA
  refine hdc78 st3 s0 sm3 g.prevCap g.prevPtr (recordCurCap g) w4 w5 w6 c_sp0
    q140 tail _ F_copy
    hprev_lt htail_len hpcm3 hrunm3 hsp_align (hspm3.trans hs3_sp) hcrlm3 hvregs_m3 hx25_m3
    (Entails.of_eq (by unfold F_copy; sep_ac_rfl))
    fun sm4 hpcm4 hrunm4 hspm4 hcrlm4 hvregsm4 htrm4
      hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx27_4 hx26_4 hx25_4 hx22_4 hx28_4 => ?_
  have hsp_al4 : sm4.spAligned = true := spAligned_sub_350 hsp_align hspm4
  have hx19_m4 : sm4.readReg64 .x19 = x.call.fut := hx19_4.trans hx19_m3
  have hx20_m4 : sm4.readReg64 .x20 = x.call.out := hx20_4.trans hx20_m3
  have hx21_m4 : sm4.readReg64 .x21 = namePtr := hx21_4.trans hx21_m3
  have hx23_m4 : sm4.readReg64 .x23 = bytesCap := hx23_4.trans hx23_m3
  have hx24_m4 : sm4.readReg64 .x24 = bytesPtr := hx24_4.trans hx24_m3
  have htr_m4 : sm4.trace = s0.trace := htrm4.trans htr_m3
  let F_some : SepProp :=
    ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
    ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
    ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
    ((s0.sp - 0x1c8#64) ↦₆₄ recordCurCap g) ∗
    ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
    ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
    ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
    recordHeap A.repAlloc g r ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    dirAt A.repAlloc x.self x.dir ∗
    protocolAddressAt A.repAlloc x.call.addr x.call.addrA
  have hdone : ∀ (evs_free : List AllocEvent) (sf : State) (P_f : SepProp),
      FreeOnlyEvs evs_free →
      sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x g.prevCap g.prevPtr 0#64 (recordCurCap g) w4
        (w6 ++ w5) tail ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
        A.pool lim (M.stepEvents evs_free st3) sf ∗ F_some) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨
          (sessLoadPollSpecPlaced rd pathOk Scope A lim LoadEnv stk).post (x, st0) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro evs_free sf P_f hfo htr_eq hsp_f hcs_f hPf
    obtain ⟨evs, hevs, hst_eq⟩ := hevs_fin evs_des evs_free hevs_des hfo
    dsimp only [st3] at hPf
    rw [hst_eq] at hPf
    have hgr_f :
        Except.ok (b0 :: bsRest) =
          x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
        sf.trace = s0.trace :=
      ⟨hgr.1, htr_eq⟩
    have hans : SessLoadAns Scope (.ok (b0 :: bsRest)) (.ok (some r)) := ⟨r, rfl, henc, hsc⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (lpoll_post_entails_placed rd pathOk Scope A lim LoadEnv stk x st0 s0 sf evs
        (.ok (b0 :: bsRest)) (.ok (some r)) hgr_f hans hevs)
    refine Entails.trans ?_
      (finish_common_reassemble_budget A lim (M.stepEvents evs st0) sf s0 x hstk hstk_hi
        (.ok (some r)) nameCap namePtr nameBs 0#64 (w6 ++ w5))
    have hrec := record_reassemble_for_poll A.repAlloc s0.sp x.call.out g r hinl
    have hgrp :
        epilogueOut s0 x g.prevCap g.prevPtr 0#64 (recordCurCap g) w4
          (w6 ++ w5) tail ∗
          ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents evs st0) sf ∗ F_some =
        (((x.call.out ↦₆₄ g.prevCap) ∗ ((x.call.out + 8#64) ↦₆₄ g.prevPtr) ∗
          ((x.call.out + 0x10#64) ↦₆₄ 0#64) ∗
          ((x.call.out + 0x18#64) ↦₆₄ recordCurCap g) ∗
          ((x.call.out + 0x20#64) ↦₆₄ w4) ∗ ((x.call.out + 0x28#64) ↦₁₂₈ (w6 ++ w5)) ∗
          ((x.call.out + 0x38#64) ↦ₛ tail) ∗
          ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
          ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 0x1c8#64) ↦₆₄ recordCurCap g) ∗
          ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗ ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
          ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
          ((s0.sp - 0x348#64) ↦ₛ tail) ∗
          recordHeap A.repAlloc g r) ∗
        ((((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
          ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ (w6 ++ w5)) ∗
          memRegion (s0.sp - 0x200#64) 8 ∗
          memRegion (s0.sp - 0x070#64) 16 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - extHookStack) ∗
          stackAt (s0.sp - 0x350#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗
          dirAt A.repAlloc x.self x.dir ∗
          protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
          A.pool lim (M.stepEvents evs st0) sf)) := by
      unfold epilogueOut F_some; sep_ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono_left hrec) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    refine SepWP.weaken_pre (P' :=
      (bytesAt false bytesPtr (encodeRecord r) ∗
        vecU8Tail A.repAlloc 0#64 bytesPtr (encodeRecord r)) ∗
      (((s0.sp - 0x348#64) ↦ₛ tail) ∗
        ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
        stackAt (s0.sp - 0x350#64) extHookStack ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ recordCurCap g) ∗
        ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
        ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
        ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ (w6 ++ w5)) ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - extHookStack) ∗
        recordHeap A.repAlloc g r ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        bytesAt false namePtr nameBs ∗
        vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A.repAlloc x.self x.dir ∗
        protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
        A.pool lim st3 sm4))
      (Entails.of_eq (by unfold F_copy; sep_ac_rfl)) ?_
    refine SepWP.weaken_pre
      (sepConj_mono_left (vecU8_free_zero A.repAlloc bytesPtr hblen)) ?_
    simp only [emp_sepConj]
    apply sepWP_seq_lscro (mid := (blkPl_569).base + 332#64) hcrlm4
    let _ := hsp_al4
    wp_steps_sync_pool ((blkPl_569).base + 332#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_14c
    try rw [state_setMem_setMem] at hcrl_14c ⊢
    refine hf14c x st3 s0 _ nameCap namePtr nameBs
      g.prevCap g.prevPtr 0#64 (recordCurCap g) w4
      (w6 ++ w5) tail _ F_some
      hnlen hnlt hnptr htail_len
      (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hcrl_14c
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (Entails.of_eq (by unfold epiloguePre F_some; sep_ac_rfl))
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone (optDeallocBufEvents nameCap) sf P_f
          (freeOnlyEvs_optDeallocBufEvents nameCap)
          (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf
  · have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    apply sepWP_seq_lscro (mid := (blkPl_569).base + 316#64) hcrlm4
    let _ := hsp_al4; let _ := hbcap_beq
    wp_steps_sync_pool ((blkPl_569).base + 316#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_13c
    try rw [state_setMem_setMem] at hcrl_13c ⊢
    refine hdb13c x st3 s0 _ bytesCap bytesPtr (encodeRecord r)
      nameCap namePtr nameBs
      g.prevCap g.prevPtr 0#64 (recordCurCap g) w4
      (w6 ++ w5) tail _ F_some
      hbcap hblen hblt hbptr hnlen hnlt hnptr htail_len
      (by simp only [arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hcrl_13c
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (Entails.of_eq (by unfold F_copy epiloguePre F_some; sep_ac_rfl))
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone (rustDeallocEvents bytesCap.toNat 1 ++ optDeallocBufEvents nameCap) sf P_f
          (FreeOnlyEvs.append (freeOnlyEvs_rustDeallocEvents bytesCap.toNat 1)
            (freeOnlyEvs_optDeallocBufEvents nameCap))
          (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

/-- Top-level budget-threaded proof of `load_session::{closure#0}` (Block `569`) against
`sessLoadPollSpecPlaced` with `CliLoadPollEnv rd Scope AddrEnv GetEnv DeserEnv`. -/
theorem sessLoadPoll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hGet : subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDeser : subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hFs : TraceFsSound ((blkPC_569).rebase (blkPl_569).base H))
    (hstk : pollMinStk addrStk getStk ≤ stk) :
    subroutine_ok ((blkPC_569).rebase (blkPl_569).base H) (blkPl_569).base
      (sessLoadPollSpecPlaced rd pathOk Scope A lim
        (CliLoadPollEnv rd Scope AddrEnv GetEnv DeserEnv) stk) := by
  let LoadEnv := CliLoadPollEnv rd Scope AddrEnv GetEnv DeserEnv
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_al0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_al0
  have hAddrFs := subroutine_ok_withFsInv hFs hAddr s0.fs.files s0.trace
  have hbrErr :=
    @lpoll_branch_err_placed _ M A lim H LoadEnv rd pathOk Scope addrStk getStk stk hC
  have hbrNil :=
    @lpoll_branch_ok_nil_placed _ M A lim H LoadEnv rd pathOk Scope addrStk getStk stk hC
  have hbrCons :=
    @lpoll_branch_ok_cons_placed _ M A lim H DeserEnv LoadEnv rd pathOk Scope
      addrStk getStk stk hC hDeser
  clear hFs hAddr hDeser hC
  refine ⟨(sessLoadPollSpecPlaced rd pathOk Scope A lim LoadEnv stk).pre (x, st0) s0, R, hpre, ?_⟩
  generalize hQ_eq :
    (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨
          (sessLoadPollSpecPlaced rd pathOk Scope A lim LoadEnv stk).post (x, st0) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q
  generalize hQp_eq :
    (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨
          (sessLoadPollSpecPlaced rd pathOk Scope A lim LoadEnv stk).onPanic (x, st0) s0 sf ∗ R)) =
      Qp
  dsimp only [sessLoadPollSpecPlaced, withLsCodeRoLoaded]
  rw [sepConj_comm]
  refine SepWPp.pure_elim fun hcrl0 => ?_
  refine SepWPp.pure_elim
    fun ⟨hx0_0, hx8_0, hname_lt, htext_lt, hdir_lt, hpOk, hwf, hfit0⟩ => ?_
  have hfit_addr : FitsEnv M lim st0 (AddrEnv x.call.addr) := FitsEnv.seq_left hfit0
  refine sepWPp_with_stk_bound (a := x.call.fut) (v := x.self)
    (Rest := ((x.call.fut + 8#64) ↦₆₄ x.call.addrA) ∗ ((x.call.fut + 0x10#64) ↦₈ 0#8) ∗
      memRegion (x.call.fut + 0x11#64) 7 ∗ dirAt A.repAlloc x.self x.dir ∗
      memRegion x.call.out 368 ∗ protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      A.pool lim st0 s0)
    (Entails.of_eq (by unfold sessLoadBoxAt; sep_ac_rfl))
    fun hstk_hi => ?_
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have haddr_le : addrStk ≤ subMax addrStk getStk := by unfold subMax; omega
  have hget_le : getStk ≤ subMax addrStk getStk := by unfold subMax; omega
  rw [stackAt_sub_split s0.sp hstk hstk_hi,
      stackAt_loadPoll_eq s0.sp hmin_hi,
      subStack_split s0.sp haddr_le hmin_hi]
  unfold sessLoadBoxAt loadPollFrameSlots
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_sp0 => SepWPp.exists_elim fun q140 =>
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 => ?_
  apply sepWPp_seq_lscro (mid := lsmpl.base 594) hcrl0
  wp_steps_sync_pool (lsmpl.base 594)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl1
  try rw [state_setMem_setMem] at hcrl1 ⊢
  refine sepWPp_name_state fun s1 hs1 => ?_
  have hs1_pc : s1.pc = lsmpl.base 594 := by
    rw [hs1]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs1_lr : s1.readReg64 Reg.lr = (blkPl_569).base + 64#64 := by
    rw [hs1]; simp only [wp_norm, arm64_norm, *]
  have hs1_run : s1.status = .Running := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_sp : s1.sp = s0.sp - 0x350#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_tr : s1.trace = s0.trace := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_fs : s1.fs = s0.fs := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x0 : s1.readReg64 .x0 = s0.sp - 0x1f8#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x1 : s1.readReg64 .x1 = x.call.addrA := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x19 : s1.readReg64 .x19 = x.call.fut := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x20 : s1.readReg64 .x20 = x.call.out := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x22 : s1.readReg64 .x22 = x.self := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x25 : s1.readReg64 .x25 = s0.sp - 0x210#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_vregs : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
    rw [hs1]; simp only [arm64_norm, *]
  rw [← hs1] at hcrl1 ⊢
  clear hs1
  let F_addr : SepProp :=
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    dirAt A.repAlloc x.self x.dir ∗
    memRegion x.call.out 368 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - addrStk) ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x348#64) 312 ∗
    ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x1e0#64) 368 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0
  refine lpoll_call_addrText_placed hAddrFs
    { addr := x.call.addrA, g := x.call.addr, ret := s0.sp - 0x1f8#64 } st0 F_addr
    hs1_pc hs1_run (spAligned_sub_350 hsp_align hs1_sp) hs1_lr hcrl1
    (by rw [← hs1_fs, ← hs1_tr]; exact FsInv.of_entry s1)
    hs1_x0 hs1_x1 hname_lt hfit_addr
    (Entails.of_eq (by
      rw [hs1_sp]
      unfold F_addr sessLoadBoxAt savedCalleeSlots
      dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.lr]
      sep_ac_rfl))
    fun sm1 evs_addr hpcm1 hrunm1 hspm1 hcsm1 hcrlm1 hfsm1 htrm1 hevs_addr => ?_
  rw [hs1_sp]
  let st1 : M.σ := M.stepEvents evs_addr st0
  have hfit1 := FitsEnv.seq_right hfit0 hevs_addr
  rcases hcsm1 with ⟨hx19_1, hx20_1, _, hx22_1, _, _, hx25_1, _, _, _, _, hvregs_1⟩
  have hsp_m1 : sm1.sp = s0.sp - 0x350#64 := hspm1.trans hs1_sp
  have hsp_al1 : sm1.spAligned = true := spAligned_sub_350 hsp_align hsp_m1
  have hx19_m1 : sm1.readReg64 .x19 = x.call.fut := hx19_1.trans hs1_x19
  have hx20_m1 : sm1.readReg64 .x20 = x.call.out := hx20_1.trans hs1_x20
  have hx22_m1 : sm1.readReg64 .x22 = x.self := hx22_1.trans hs1_x22
  have hx25_m1 : sm1.readReg64 .x25 = s0.sp - 0x210#64 := hx25_1.trans hs1_x25
  have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := hvregs_1.trans hs1_vregs
  have htr_m1 : sm1.trace = s0.trace := htrm1.trans hs1_tr
  have hfiles_m1 : sm1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfsm1 htr_m1
  let nameBs := addressText x.call.addr.val
  have hfit_get : FitsEnv M lim st1 (GetEnv s0.fs.files x.dir nameBs) := FitsEnv.seq_left hfit1
  have hrestk1 :
      stackAt (s0.sp - 0x350#64) addrStk ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - addrStk) =
      memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
        (subMax addrStk getStk - getStk) ∗
      stackAt (s0.sp - 0x350#64) getStk := by
    rw [sepConj_comm, ← subStack_split s0.sp haddr_le hmin_hi,
        subStack_split s0.sp hget_le hmin_hi]
  unfold F_addr
  rw [vecU8_eq_bytes_tail A.repAlloc (s0.sp - 0x1f8#64) nameBs (s0.sp - 0x1f0#64)
        (s0.sp - 0x1e8#64) (by bv_omega) (by bv_omega),
      slot170_split48 s0.sp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun nameCap => SepWPp.exists_elim fun namePtr =>
    SepWPp.pure_elim fun ⟨hnlen, hnlt, hnptr⟩ => ?_
  refine sepWPp_conseq
    (P' := ((stackAt (s0.sp - 0x350#64) addrStk ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - addrStk)) ∗
      ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
      ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
      ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      A.pool lim st1 sm1 ∗
      sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
      dirAt A.repAlloc x.self x.dir ∗
      memRegion x.call.out 368 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
      ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
      memRegion (s0.sp - 0x348#64) 312 ∗
      ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
      memRegion (s0.sp - 0x200#64) 8 ∗
      memRegion (s0.sp - 0x1e0#64) 48 ∗
      memRegion (s0.sp - 0x1b0#64) 320 ∗
      memRegion (s0.sp - 0x070#64) 16 ∗
      savedCalleeSlots s0))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  rw [hrestk1]
  simp only [sepConj_assoc]
  apply sepWPp_seq_lscro (mid := lsmpl.base 589) hcrlm1
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl2
  try rw [state_setMem_setMem] at hcrl2 ⊢
  have hx3_len : (BitVec.ofNat 64 nameBs.length).toNat = nameBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_name_state fun s2 hs2 => ?_
  have hs2_pc : s2.pc = lsmpl.base 589 := by
    rw [hs2]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs2_lr : s2.readReg64 Reg.lr = (blkPl_569).base + 84#64 := by
    rw [hs2]; simp only [wp_norm, arm64_norm, *]
  have hs2_run : s2.status = .Running := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_sp : s2.sp = s0.sp - 0x350#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_tr : s2.trace = s0.trace := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_files : s2.fs.files = s0.fs.files := by
    have hs2_fs : s2.fs = sm1.fs := by rw [hs2]; simp only [arm64_norm, *]
    rw [hs2_fs]; exact hfiles_m1
  have hs2_x0 : s2.readReg64 .x0 = s0.sp - 0x1e0#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x1 : s2.readReg64 .x1 = x.self := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x2 : s2.readReg64 .x2 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x3 : (s2.readReg64 .x3).toNat = nameBs.length := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_x19 : s2.readReg64 .x19 = x.call.fut := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x20 : s2.readReg64 .x20 = x.call.out := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x21 : s2.readReg64 .x21 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x25 : s2.readReg64 .x25 = s0.sp - 0x210#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_vregs : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
    rw [hs2]; simp only [arm64_norm, *]
  rw [← hs2] at hcrl2 ⊢
  clear hs2
  let F_get : SepProp :=
    memRegion (s0.sp - 0x1b0#64) 320 ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x348#64) 312 ∗
    ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - getStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion x.call.out 368 ∗
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    protocolAddressAt A.repAlloc x.call.addr x.call.addrA
  refine lpoll_call_dirGet_placed hGet
    { ret := s0.sp - 0x1e0#64, self := x.self, dir := x.dir,
      nameA := namePtr, name := nameBs, nameRo := false } st1 F_get
    hs2_pc hs2_run (spAligned_sub_350 hsp_align hs2_sp) hs2_lr hcrl2
    hs2_x0 hs2_x1 hs2_x2 hs2_x3
    htext_lt hdir_lt hpOk (by rw [hs2_files]; exact hfit_get)
    (Entails.of_eq (by rw [hs2_sp]; unfold F_get; dsimp only; sep_ac_rfl))
    fun sm2 evs_get gr hpcm2 hrunm2 hspm2 hcsm2 hcrlm2 hgr => ?_
  rw [hs2_sp]
  let st2 : M.σ := M.stepEvents evs_get st1
  rcases hcsm2 with ⟨hx19_2, hx20_2, hx21_2, _, _, _, hx25_2, _, _, _, _, hvregs_2⟩
  have hsp_m2 : sm2.sp = s0.sp - 0x350#64 := hspm2.trans hs2_sp
  have hx19_m2 : sm2.readReg64 .x19 = x.call.fut := hx19_2.trans hs2_x19
  have hx20_m2 : sm2.readReg64 .x20 = x.call.out := hx20_2.trans hs2_x20
  have hx21_m2 : sm2.readReg64 .x21 = namePtr := hx21_2.trans hs2_x21
  have hx25_m2 : sm2.readReg64 .x25 = s0.sp - 0x210#64 := hx25_2.trans hs2_x25
  have hvregs_m2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := hvregs_2.trans hs2_vregs
  have hevs_get : GetEnv s0.fs.files x.dir nameBs evs_get := by
    simpa only [nameBs, hs2_files] using hgr.2.2
  have hfit2 := FitsEnv.seq_right hfit1 hevs_get
  have hgr0 :
      gr = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧ sm2.trace = s0.trace :=
    ⟨by simpa only [nameBs, hs2_files] using hgr.1, hgr.2.1.trans hs2_tr⟩
  clear hs2_files hgr
  have hpost_get :
      ((getResultAt A.repAlloc (s0.sp - 0x1e0#64) gr ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt false namePtr nameBs ∗
        stackAt (s0.sp - 0x350#64) getStk ∗ A.pool lim st2 sm2) ∗ F_get) ⊢
      getResultAt A.repAlloc (s0.sp - 0x1e0#64) gr ∗
        postGetCommon (A.atState lim st2 sm2) s0 x addrStk getStk stk
          nameCap namePtr nameBs c_sp0 q140 := by
    have hstk_merge :
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - getStk) ∗
        stackAt (s0.sp - 0x350#64) getStk =
        stackAt (s0.sp - 0x350#64) (subMax addrStk getStk) :=
      (subStack_split s0.sp hget_le hmin_hi).symm
    rw [postGetCommon_atState]
    unfold F_get
    have hpull :
        ((getResultAt A.repAlloc (s0.sp - 0x1e0#64) gr ∗ dirAt A.repAlloc x.self x.dir ∗
          bytesAt false namePtr nameBs ∗
          stackAt (s0.sp - 0x350#64) getStk ∗ A.pool lim st2 sm2) ∗
          memRegion (s0.sp - 0x1b0#64) 320 ∗
          ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
          vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
          memRegion (s0.sp - 0x348#64) 312 ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
          memRegion (s0.sp - 0x200#64) 8 ∗
          memRegion (s0.sp - 0x070#64) 16 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - getStk) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
          memRegion x.call.out 368 ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
          protocolAddressAt A.repAlloc x.call.addr x.call.addrA) =
        ((memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - getStk) ∗
          stackAt (s0.sp - 0x350#64) getStk) ∗
          (getResultAt A.repAlloc (s0.sp - 0x1e0#64) gr ∗
            memRegion (s0.sp - 0x1b0#64) 320 ∗
            ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
            bytesAt false namePtr nameBs ∗
            vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
            ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
            memRegion (s0.sp - 0x348#64) 312 ∗
            ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
            memRegion (s0.sp - 0x200#64) 8 ∗
            memRegion (s0.sp - 0x070#64) 16 ∗
            savedCalleeSlots s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
            memRegion x.call.out 368 ∗
            sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
            dirAt A.repAlloc x.self x.dir ∗
            protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
            A.pool lim st2 sm2)) := by
      sep_ac_rfl
    rw [hpull, hstk_merge]
    exact Entails.of_eq (by sep_ac_rfl)
  refine sepWPp_conseq hpost_get ?_
  subst hQ_eq hQp_eq
  rcases gr with ⟨⟩ | ⟨_ | ⟨b0, bsRest⟩⟩
  · apply sepWPp_of_sepWP_final
    refine hbrErr x st0 st2 R s0 sm2 nameCap namePtr nameBs c_sp0 q140
      hstk hstk_hi hnlen hnlt hnptr hgr0 ?_
      hpcm2 hrunm2 hsp_align hsp_m2 hcrlm2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx25_m2
    intro evs_free hfo
    refine ⟨evs_addr ++ (evs_get ++ evs_free), ?_, ?_⟩
    · refine SeqEnv.append hevs_addr (SeqEnv.append hevs_get ?_)
      have hopt :
          OptLoadDeserEnv Scope DeserEnv
            (x.dir.get rd s0.fs.files (addressText x.call.addr.val)) [] := by
        rw [← hgr0.1]; rfl
      simpa only [List.nil_append] using SeqEnv.append hopt hfo
    · simp only [st2, st1, M.stepEvents_append]
  · apply sepWPp_of_sepWP_final
    refine hbrNil x st0 st2 R s0 sm2 nameCap namePtr nameBs c_sp0 q140
      hstk hstk_hi hnlen hnlt hnptr hgr0 ?_
      hpcm2 hrunm2 hsp_align hsp_m2 hcrlm2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx25_m2
    intro evs_free hfo
    refine ⟨evs_addr ++ (evs_get ++ evs_free), ?_, ?_⟩
    · refine SeqEnv.append hevs_addr (SeqEnv.append hevs_get ?_)
      have hopt :
          OptLoadDeserEnv Scope DeserEnv
            (x.dir.get rd s0.fs.files (addressText x.call.addr.val)) [] := by
        rw [← hgr0.1]; rfl
      simpa only [List.nil_append] using SeqEnv.append hopt hfo
    · simp only [st2, st1, M.stepEvents_append]
  · rcases hwf (b0 :: bsRest) hgr0.1.symm with hbad | ⟨r, henc, hsc⟩
    · cases hbad
    · have hfit_des : FitsEnv M lim st2 (DeserEnv r) := by
        refine FitsEnv.mono (fun evs h => ?_) (FitsEnv.seq_left hfit2)
        rw [← hgr0.1]
        exact ⟨r, henc, hsc, h⟩
      refine hbrCons x st0 st2 R s0 sm2 r b0 bsRest nameCap namePtr nameBs c_sp0 q140
        hstk hstk_hi hnlen hnlt hnptr henc hsc hgr0 hfit_des ?_
        hpcm2 hrunm2 hsp_align hsp_m2 hcrlm2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx25_m2
      intro evs_des evs_free hevs_des hfo
      refine ⟨evs_addr ++ (evs_get ++ (evs_des ++ evs_free)), ?_, ?_⟩
      · refine SeqEnv.append hevs_addr (SeqEnv.append hevs_get ?_)
        have hopt :
            OptLoadDeserEnv Scope DeserEnv
              (x.dir.get rd s0.fs.files (addressText x.call.addr.val)) evs_des := by
          rw [← hgr0.1]
          exact ⟨r, henc, hsc, hevs_des⟩
        exact SeqEnv.append hopt hfo
      · simp only [st2, st1, M.stepEvents_append]

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.SymPlacedBudget
