/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.BranchesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.EpiloguePlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Branch Proofs for `remove_pre_key::{closure#0}`

Budget-threaded `Err`, `Ok([])`, and `Ok(b0 :: bsRest)` branch proofs for Block `575`
(`lsProg_575 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.BranchesPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speAt speWord)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost PkPollGhost ReadRule dirAt getResultAt keyName pkBoxAt pkRemoveOf pkRemoveOutAt utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_575 blkPl_575)
open CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
  (calleeSavedVRegs_writeVReg128_0 epilogueOut epiloguePre extractLsb_0_64_append_p
   extractLsb_64_64_append_p fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState
   fs_writeReg fs_writeReg32 fs_writeReg64 fs_writeVReg128 getResultAt_ok_unpack_placed
   header3_entails_memRegion24 layoutOk_u8_of_ne_zero okTagVec_add_two_eq_zero
   pkRemoveOutAt_ok_reassemble pollMinStk restore_pollStack savedCalleeSlots sepWP_to_sepWPp_placed
   sepWPp_conseq sepWPp_name_state_placed sepWPp_of_sepWP_final_placed setWidth_32_setWidth_64
   setWidth_64_append_p slot_a8_err_collapse slot_a8_ok_collapse slot_a8_put_collapse
   spAligned_sub_c0 speAt_read_invalidState_eq speAt_read_invalidState_intro speReadHeap
   speWord_one_add_two_ne_zero subMax subStack_split vecU8Tail vecU8_empty_of_zero_one_zero
   vecU8_free_ne vecU8_free_zero)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   SeqEnv rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced decimalSpecPlaced dirPutSpecPlaced pkRemovePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv OptPkRemoveTailEnv freeOnlyEvs_optDeallocBufEvents
   freeOnlyEvs_rustDeallocEvents pkrm_call_decimal_placed pkrm_call_dirPut_placed
   pkrm_dealloc_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.EpiloguePlacedBudget
  (pkrm_drop_both_6c_placed pkrm_epilogue_108_placed pkrm_finish_f4_placed)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0 setWidth_32_setWidth_64
  extractLsb_0_64_append_p extractLsb_64_64_append_p setWidth_64_append_p
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

theorem finish_common_reassemble_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 sf : State) (x : PkPollGhost)
    {decStk getStk putStk stk : Nat}
    (hstk : pollMinStk decStk getStk putStk ≤ stk) (hstk_hi : stk ≤ 2 ^ 64)
    (res : Except Unit Unit × DirGhost) (q_sp0 : BitVec 128) :
    (pkRemoveOutAt A.repAlloc x.out res.1 ∗
      dirAt A.repAlloc x.self res.2 ∗
      memRegion (s0.sp - 0xa8#64) 48 ∗
      memRegion (s0.sp - 0x78#64) 24 ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
      memRegion (s0.sp - 0xb0#64) 8 ∗
      savedCalleeSlots s0 ∗
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xc0#64) extHookStack ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      pkBoxAt x.fut x.self x.id 1#8 ∗
      A.pool lim st sf) ⊢
    pkRemoveOutAt A.repAlloc x.out res.1 ∗ dirAt A.repAlloc x.self res.2 ∗
      pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool lim st sf ∗ stackAt s0.sp stk := by
  have hrstk := restore_pollStack s0 hstk hstk_hi q_sp0
  have hgroup :
      (pkRemoveOutAt A.repAlloc x.out res.1 ∗
        dirAt A.repAlloc x.self res.2 ∗
        memRegion (s0.sp - 0xa8#64) 48 ∗
        memRegion (s0.sp - 0x78#64) 24 ∗
        ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
        memRegion (s0.sp - 0xb0#64) 8 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - extHookStack) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
        pkBoxAt x.fut x.self x.id 1#8 ∗
        A.pool lim st sf) =
      ((pkRemoveOutAt A.repAlloc x.out res.1 ∗ dirAt A.repAlloc x.self res.2 ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool lim st sf) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          memRegion (s0.sp - 0xa8#64) 48 ∗
          memRegion (s0.sp - 0x78#64) 24 ∗
          savedCalleeSlots s0)) := by
    sep_ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right hrstk) ?_
  exact Entails.of_eq (by sep_ac_rfl)

def postGetCommon_placed {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 sm2 : State) (x : PkPollGhost)
    (decStk getStk putStk stk : Nat)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128) : SepProp :=
  ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
  ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
  ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
  bytesAt false namePtr nameBs ∗
  vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
  ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
  memRegion (s0.sp - 0xb0#64) 8 ∗
  savedCalleeSlots s0 ∗
  stackAt (s0.sp - 0xc0#64) (subMax decStk getStk putStk) ∗
  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
  memRegion x.out 48 ∗
  pkBoxAt x.fut x.self x.id 0#8 ∗
  dirAt A.repAlloc x.self x.dir ∗
  A.pool lim st sm2

theorem pkrm_post_entails_placed [LibsignalPlacement] {M : AllocCostModel}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (RemEnv : FsFiles → PkPollGhost → List AllocEvent → Prop)
    (stk : Nat) (x : PkPollGhost) (st0 : M.σ) (evs : List AllocEvent) (s0 sf : State)
    (res : Except Unit Unit × DirGhost)
    (hres : res = pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
      sf.trace = s0.trace ∧ RemEnv s0.fs.files x evs) :
    (pkRemoveOutAt A.repAlloc x.out res.1 ∗ dirAt A.repAlloc x.self res.2 ∗
      pkBoxAt x.fut x.self x.id 1#8 ∗ A.pool lim (M.stepEvents evs st0) sf ∗
      stackAt s0.sp stk) ⊢
      (pkRemovePollSpecPlaced rd pathOk A lim RemEnv stk).post (x, st0) s0 sf := by
  simp only [pkRemovePollSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left,
    sepConj_assoc]
  exact Entails.sepExists_right evs
    (Entails.sepExists_right res (Entails.pure_right hres (Entails.refl _)))

/-- Branch A (`+0x058` on `gr = .error ()`) on Block `575`: frees `name` if `nameCap ≠ 0`, moves the
48-byte SPE to `out`, leaves `dirAt` unchanged, and returns `(.error (), x.dir)`. -/
theorem pkrm_branch_err_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : PkPollGhost) (st0 : M.σ) (evs1 evs2 : List AllocEvent)
    (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hevs1 : DecEnv x.id evs1)
    (hevs2 : GetEnv s0.fs.files x.dir (keyName x.id) evs2)
    (hgr : Except.error () = x.dir.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_575).base + 88#64)
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx21 : sm2.readReg64 .x21 = namePtr) :
    SepWP ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A.repAlloc (s0.sp - 0xa8#64) (.error ()) ∗
        postGetCommon_placed A lim (M.stepEvents evs2 (M.stepEvents evs1 st0)) s0 sm2 x
          decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A lim
            (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hne : (speWord 1 + 2#64 == 0#64) = false := speWord_one_add_two_ne_zero
  have hep := @pkrm_epilogue_108_placed _ M A lim H
  let st2 := M.stepEvents evs2 (M.stepEvents evs1 st0)
  unfold postGetCommon_placed
  change SepWP _ _ _ (speAt A.repAlloc (utf8 "read") (s0.sp - 0xa8#64) .invalidState ∗ _) _
  rw [speAt_read_invalidState_eq A.repAlloc (s0.sp - 0xa8#64) (s0.sp - 0xa0#64) (s0.sp - 0x98#64)
        (s0.sp - 0x90#64) (s0.sp - 0x88#64)
        (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega),
      subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun errBs => SepWP.exists_elim fun errCap =>
    SepWP.exists_elim fun errPtr => SepWP.exists_elim fun fnPtr => ?_
  let q_err : BitVec 128 := BitVec.ofNat 64 (utf8 "read").length ++ fnPtr
  let F_err : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa0#64) ↦₆₄ errCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ errPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
    ((s0.sp - 0x88#64) ↦₁₂₈ q_err) ∗
    speReadHeap A.repAlloc errBs errCap errPtr fnPtr ∗
    ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    dirAt A.repAlloc x.self x.dir
  let evs_tot := evs1 ++ (evs2 ++ optDeallocBufEvents nameCap)
  have hevs_tot : CliPkRemovePollEnv rd DecEnv GetEnv PutEnv s0.fs.files x evs_tot := by
    unfold CliPkRemovePollEnv
    refine SeqEnv.append hevs1 (SeqEnv.append hevs2 ?_)
    rw [← hgr.1]
    exact freeOnlyEvs_optDeallocBufEvents nameCap
  have hst_tot : M.stepEvents evs_tot st0 = M.stepEvents (optDeallocBufEvents nameCap) st2 := by
    simp only [evs_tot, st2, M.stepEvents_append]
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err ∗
        A.pool lim (M.stepEvents (optDeallocBufEvents nameCap) st2) sf ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗ F_err) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A lim
          (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f :
        (Except.error (), x.dir) =
          pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace ∧
        CliPkRemovePollEnv rd DecEnv GetEnv PutEnv s0.fs.files x evs_tot :=
      ⟨by rw [← hgr.1]; rfl, htr_eq.trans hgr.2, hevs_tot⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    rw [← hst_tot]
    refine Entails.trans ?_
      (pkrm_post_entails_placed rd pathOk A lim
        (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk x st0 evs_tot s0 sf
        (.error (), x.dir) hres_f)
    refine Entails.trans ?_
      (finish_common_reassemble_placed A lim (M.stepEvents evs_tot st0) s0 sf x hstk hstk_hi
        (.error (), x.dir) q_err)
    have hout := speAt_read_invalidState_intro A.repAlloc x.out errBs errCap errPtr fnPtr
    have hslot := slot_a8_err_collapse s0.sp (speWord 1) errCap errPtr
      (BitVec.ofNat 64 errBs.length) q_err
    have h24 := header3_entails_memRegion24 (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
      nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
    have hgrp :
        epilogueOut s0 x (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err ∗
          A.pool lim (M.stepEvents evs_tot st0) sf ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗ F_err =
        (((x.out ↦₆₄ speWord 1) ∗ ((x.out + 8#64) ↦₆₄ errCap) ∗
          ((x.out + 0x10#64) ↦₆₄ errPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((x.out + 0x20#64) ↦₁₂₈ q_err) ∗
          speReadHeap A.repAlloc errBs errCap errPtr fnPtr) ∗
        (((s0.sp - 0xa8#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa0#64) ↦₆₄ errCap) ∗
          ((s0.sp - 0x98#64) ↦₆₄ errPtr) ∗
          ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((s0.sp - 0x88#64) ↦₁₂₈ q_err)) ∗
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
        (dirAt A.repAlloc x.self x.dir ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_err) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗
          A.pool lim (M.stepEvents evs_tot st0) sf)) := by
      unfold epilogueOut F_err q_err; sep_ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hout (sepConj_mono hslot (sepConj_mono_left h24))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hb8 : s0.sp - 0xc0#64 + 8#64 = s0.sp - 184#64 := by bv_omega
  have h80 : s0.sp - 0x88#64 + 8#64 = s0.sp - 128#64 := by bv_omega
  unfold Arm64.pointsTo128
  simp only [hb8, h80, extractLsb_0_64_append_p, extractLsb_64_64_append_p, sepConj_assoc]
  by_cases hncap : nameCap = 0#64
  · subst hncap
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil] at hdone
    refine SepWP.fold (vecU8_free_zero A.repAlloc namePtr hnlen) (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrl
    wp_steps_sync_pool ((blkPl_575).base + 264#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro _hcrl_108
    refine hep x st2 s0 _
      (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err _
      (stackAt (s0.sp - 0xc0#64) extHookStack ∗ F_err)
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
      (by
        unfold epiloguePre F_err q_err Arm64.pointsTo128
        simp only [hb8, h80, extractLsb_0_64_append_p, extractLsb_64_64_append_p, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)))
  · obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
    have hlay : RustLayoutOk nameCap.toNat 1 := ⟨⟨hcap_pos, hpow1, hcap_hi⟩, by decide⟩
    have hdealloc := pkrm_dealloc_placed_ok hC
    dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack] at hdealloc
    have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    simp only [optDeallocBufEvents, hncap, ↓reduceIte] at hdone
    refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_da
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 220#64) hcrl_da
    rcases hcrl_da with ⟨hcl_da, _⟩
    wp_call hdealloc (namePtr, nameCap.toNat, 1, st2)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_dc
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrl_dc
    wp_steps_sync_pool ((blkPl_575).base + 264#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro _hcrl_108
    refine hep x (M.stepEvents (rustDeallocEvents nameCap.toNat 1) st2) s0 _
      (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length) q_err _
      (stackAt (s0.sp - 0xc0#64) extHookStack ∗ F_err)
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
      (by
        unfold epiloguePre F_err q_err Arm64.pointsTo128
        simp only [hsp, hb8, h80, extractLsb_0_64_append_p, extractLsb_64_64_append_p, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)))

/-- Branch B (`+0x058` on `gr = .ok []`) on Block `575`: frees `bytes` and `name` if `cap ≠ 0`,
stores `-2` at `[out]`, leaves `dirAt` unchanged, and returns `(.ok (), x.dir)`. -/
theorem pkrm_branch_ok_nil_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : PkPollGhost) (st0 : M.σ) (evs1 evs2 : List AllocEvent)
    (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hevs1 : DecEnv x.id evs1)
    (hevs2 : GetEnv s0.fs.files x.dir (keyName x.id) evs2)
    (hgr : Except.ok ([] : List (BitVec 8)) = x.dir.get rd s0.fs.files (keyName x.id) ∧
      sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_575).base + 88#64)
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx21 : sm2.readReg64 .x21 = namePtr) :
    SepWP ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A.repAlloc (s0.sp - 0xa8#64) (.ok []) ∗
        postGetCommon_placed A lim (M.stepEvents evs2 (M.stepEvents evs1 st0)) s0 sm2 x
          decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A lim
            (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hff4 := pkrm_finish_f4_placed hC
  let st2 := M.stepEvents evs2 (M.stepEvents evs1 st0)
  unfold postGetCommon_placed
  rw [getResultAt_ok_unpack_placed A.repAlloc s0.sp [], subStack_split s0.sp hext_le hmin_hi]
  simp only [List.length_nil, sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun bytesCap => SepWP.exists_elim fun bytesPtr =>
    SepWP.pure_elim fun ⟨_hblen, hblt, _hbptr⟩ => ?_
  let F_nil : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ 0#64) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    dirAt A.repAlloc x.self x.dir
  let evs_tail := optDeallocBufEvents bytesCap ++ optDeallocBufEvents nameCap
  let evs_tot := evs1 ++ (evs2 ++ evs_tail)
  have hevs_tot : CliPkRemovePollEnv rd DecEnv GetEnv PutEnv s0.fs.files x evs_tot := by
    unfold CliPkRemovePollEnv
    refine SeqEnv.append hevs1 (SeqEnv.append hevs2 ?_)
    rw [← hgr.1]
    exact (freeOnlyEvs_optDeallocBufEvents bytesCap).append (freeOnlyEvs_optDeallocBufEvents nameCap)
  have hst_tot : M.stepEvents evs_tot st0 = M.stepEvents evs_tail st2 := by
    simp only [evs_tot, st2, M.stepEvents_append]
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x okTagVec bytesCap bytesPtr 0#64 q_sp0 ∗
        ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗
        A.pool lim (M.stepEvents evs_tail st2) sf ∗ F_nil) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A lim
          (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f :
        (Except.ok (), x.dir) =
          pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace ∧
        CliPkRemovePollEnv rd DecEnv GetEnv PutEnv s0.fs.files x evs_tot :=
      ⟨by rw [← hgr.1]; rfl, htr_eq.trans hgr.2, hevs_tot⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    rw [← hst_tot]
    refine Entails.trans ?_
      (pkrm_post_entails_placed rd pathOk A lim
        (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk x st0 evs_tot s0 sf
        (.ok (), x.dir) hres_f)
    refine Entails.trans ?_
      (finish_common_reassemble_placed A lim (M.stepEvents evs_tot st0) s0 sf x hstk hstk_hi
        (.ok (), x.dir) q_sp0)
    have hok := pkRemoveOutAt_ok_reassemble A.repAlloc x.out bytesCap bytesPtr 0#64 q_sp0
    have hslot := slot_a8_ok_collapse s0.sp okTagVec bytesCap bytesPtr 0#64
    have h24 := header3_entails_memRegion24 (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
      nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
    have hgrp :
        epilogueOut s0 x okTagVec bytesCap bytesPtr 0#64 q_sp0 ∗
          ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          A.pool lim (M.stepEvents evs_tot st0) sf ∗ F_nil =
        (((x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.out + 8#64) ↦₆₄ bytesCap) ∗ ((x.out + 0x10#64) ↦₆₄ bytesPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ 0#64) ∗ ((x.out + 0x20#64) ↦₁₂₈ q_sp0)) ∗
        (((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗ ((s0.sp - 0x90#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 0x88#64) 16) ∗
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
        (dirAt A.repAlloc x.self x.dir ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗
          A.pool lim (M.stepEvents evs_tot st0) sf)) := by
      unfold epilogueOut F_nil okTagVec; sep_ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hok (sepConj_mono hslot (sepConj_mono_left h24))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    have htail_eq : evs_tail = optDeallocBufEvents nameCap := by
      simp only [evs_tail, optDeallocBufEvents, ↓reduceIte, List.nil_append]
    rw [htail_eq] at hdone
    refine SepWP.fold (vecU8_free_zero A.repAlloc bytesPtr (bs := []) (Nat.zero_le _))
      (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 244#64) hcrl
    wp_steps_sync_pool ((blkPl_575).base + 244#64)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_f4
    refine hff4 x st2 s0 _ nameCap namePtr nameBs okTagVec 0#64 bytesPtr 0#64 q_sp0 _ F_nil
      hnlen hnlt hnptr
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hcrl_f4
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_nil; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf
  · obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
    have hlay_b : RustLayoutOk bytesCap.toNat 1 := ⟨⟨hb_pos, hb_pow1, hb_hi⟩, by decide⟩
    have hdealloc := pkrm_dealloc_placed_ok hC
    dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack] at hdealloc
    have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    have htail_eq :
        M.stepEvents evs_tail st2 =
          M.stepEvents (optDeallocBufEvents nameCap)
            (M.stepEvents (rustDeallocEvents bytesCap.toNat 1) st2) := by
      simp only [evs_tail, optDeallocBufEvents, hbcap, ↓reduceIte, M.stepEvents_append]
    rw [htail_eq] at hdone
    refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := bytesPtr) hbcap (Nat.zero_le _) hblt)
      (by sep_focus) ?_
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
    intro hcrl_da
    apply sepWP_seq_lscro (mid := (blkPl_575).base + 244#64) hcrl_da
    rcases hcrl_da with ⟨hcl_da, _⟩
    wp_call hdealloc (bytesPtr, bytesCap.toNat, 1, st2)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_f4
    refine hff4 x (M.stepEvents (rustDeallocEvents bytesCap.toNat 1) st2) s0 _
      nameCap namePtr nameBs okTagVec bytesCap bytesPtr 0#64 q_sp0 _ F_nil
      hnlen hnlt hnptr
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hcrl_f4
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre F_nil; simp only [hsp, sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

/-- Branch C (`+0x058` on `gr = .ok (b0 :: bsRest)`) on Block `575`: frees `bytes` and `name`, calls
`decimal` again, materializes empty `Vec<u8>` `[0, 1, 0]` at `sp + 0x18`, calls `Dir::put::<String>`
to set `x.dir.put (keyName x.id) []`, and returns `(.ok (), x.dir.put (keyName x.id) [])`. -/
theorem pkrm_branch_ok_cons_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat} {Qp : State → SepProp → Prop}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDec : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hPut : subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (x : PkPollGhost) (st0 : M.σ) (evs1 evs2 : List AllocEvent)
    (R : SepProp) (s0 sm2 : State)
    (b0 : BitVec 8) (bsRest : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (q_sp0 : BitVec 128)
    (hstk : pollMinStk decStk getStk putStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hdchg : x.dir.changed.length < 2 ^ 32)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hevs1 : DecEnv x.id evs1)
    (hevs2 : GetEnv s0.fs.files x.dir (keyName x.id) evs2)
    (hfit2 : FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st0))
      (OptPkRemoveTailEnv DecEnv PutEnv x (.ok (b0 :: bsRest))))
    (hgr : Except.ok (b0 :: bsRest) = x.dir.get rd s0.fs.files (keyName x.id) ∧
      sm2.trace = s0.trace)
    (hpc : sm2.pc = (blkPl_575).base + 88#64)
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0xc0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl sm2.mem)
    (hx28 : sm2.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx21 : sm2.readReg64 .x21 = namePtr)
    (hx22 : sm2.readReg64 .x22 = x.self)
    (hx23 : sm2.readReg64 .x23 = BitVec.setWidth 64 x.id) :
    SepWPp ((blkPC_575).rebase (blkPl_575).base H) (s0.readReg64 Reg.lr) sm2
      (getResultAt A.repAlloc (s0.sp - 0xa8#64) (.ok (b0 :: bsRest)) ∗
        postGetCommon_placed A lim (M.stepEvents evs2 (M.stepEvents evs1 st0)) s0 sm2 x
          decStk getStk putStk stk nameCap namePtr nameBs q_sp0)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A lim
            (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hmin_hi : pollMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdec_le : decStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hput_le : putStk ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hext_le : extHookStack ≤ subMax decStk getStk putStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hdb6c := @pkrm_drop_both_6c_placed _ M A lim H hC
  have hep := @pkrm_epilogue_108_placed _ M A lim H
  clear hC
  let st2 := M.stepEvents evs2 (M.stepEvents evs1 st0)
  unfold postGetCommon_placed
  rw [getResultAt_ok_unpack_placed A.repAlloc s0.sp (b0 :: bsRest),
      subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => SepWPp.exists_elim fun bytesPtr =>
    SepWPp.pure_elim fun ⟨hblen, hblt, hbptr⟩ => ?_
  have hbcap : bytesCap ≠ 0#64 := by
    intro hc; subst hc
    simp at hblen
  have hlen_beq : (BitVec.ofNat 64 (b0 :: bsRest).length == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have h1 := congrArg BitVec.toNat heq
    have h2 : bsRest.length + 1 < 2 ^ 64 := by
      have : (b0 :: bsRest).length = bsRest.length + 1 := rfl
      omega
    simp only [List.length_cons, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at h1
    exact Nat.succ_ne_zero _ h1
  let F_drop : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8 ∗
    dirAt A.repAlloc x.self x.dir
  apply sepWP_to_sepWPp_placed (mid := (blkPl_575).base + 148#64) hcrl
  apply sepWP_seq_lscro (mid := (blkPl_575).base + 108#64) hcrl
  wp_steps_sync_pool ((blkPl_575).base + 108#64)
  let _ := hlen_beq
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_6c
  refine hdb6c st2 s0 _ bytesCap bytesPtr (b0 :: bsRest) nameCap namePtr nameBs _ F_drop
    hbcap hblen hblt hbptr hnlen hnlt hnptr
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hsp_align
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    hcrl_6c
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by unfold F_drop; sep_focus)
    fun sm3 hpcm3 hrunm3 hspm3 _hcrlm3 htrm3
      hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 hvregs_3 => ?_
  apply SepWP.done hpcm3 (by wp_norm_lhs)
  intro hcrlm3
  let evsDrop := rustDeallocEvents bytesCap.toNat 1 ++ optDeallocBufEvents nameCap
  let st3 := M.stepEvents evsDrop st2
  have hfreeDrop : FreeOnlyEvs evsDrop :=
    (freeOnlyEvs_rustDeallocEvents bytesCap.toNat 1).append
      (freeOnlyEvs_optDeallocBufEvents nameCap)
  have hfit3 : FitsEnv M lim st3 (SeqEnv (DecEnv x.id) (PutEnv x.dir (keyName x.id) [])) := by
    dsimp only [OptPkRemoveTailEnv] at hfit2
    exact hfit2.seq_right hfreeDrop
  have hx19_m3 : sm3.readReg64 .x19 = x.fut := hx19_3.trans (by simp only [arm64_norm, *])
  have hx20_m3 : sm3.readReg64 .x20 = x.out := hx20_3.trans (by simp only [arm64_norm, *])
  have hx22_m3 : sm3.readReg64 .x22 = x.self := hx22_3.trans (by simp only [arm64_norm, *])
  have hx23_m3 : sm3.readReg64 .x23 = BitVec.setWidth 64 x.id :=
    hx23_3.trans (by simp only [arm64_norm, *])
  have hx24_m3 : sm3.readReg64 .x24 = bytesCap := hx24_3
  have hx25_m3 : sm3.readReg64 .x25 = bytesPtr := hx25_3
  have hx26_m3 : sm3.readReg64 .x26 = okTagVec := hx26_3.trans (by simp only [arm64_norm, *])
  have hx27_m3 : sm3.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length :=
    hx27_3.trans (by simp only [arm64_norm, *])
  have htr_m3 : sm3.trace = s0.trace :=
    htrm3.trans (by simp only [hgr.2, arm64_norm, *])
  have hsp_al3 : sm3.spAligned = true := spAligned_sub_c0 hsp_align hspm3
  clear htrm3 hx19_3 hx20_3 hx22_3 hx23_3 hx26_3 hx27_3 hdb6c
  have hrestk_dec :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xc0#64) extHookStack =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - decStk) ∗
      stackAt (s0.sp - 0xc0#64) decStk := by
    rw [← subStack_split s0.sp hext_le hmin_hi, subStack_split s0.sp hdec_le hmin_hi]
  have h24_name := header3_entails_memRegion24
    (s0.sp - 0x78#64) (s0.sp - 0x70#64) (s0.sp - 0x68#64)
    nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
  let F_dec2 : SepProp :=
    ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - decStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8 ∗
    dirAt A.repAlloc x.self x.dir
  have hprep_dec :
      (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗
        A.pool lim st3 sm3 ∗ F_drop) ⊢
      (memRegion (s0.sp - 0x78#64) 24 ∗ stackAt (s0.sp - 0xc0#64) decStk ∗
        A.pool lim st3 sm3) ∗ F_dec2 := by
    have hpull :
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          A.pool lim st3 sm3 ∗ F_drop) =
        ((((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x70#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
          (memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
              (subMax decStk getStk putStk - extHookStack) ∗
            stackAt (s0.sp - 0xc0#64) extHookStack) ∗
          A.pool lim st3 sm3 ∗
          (((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
            ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
            ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
            ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
            memRegion (s0.sp - 0x88#64) 16 ∗
            ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
            memRegion (s0.sp - 0xb0#64) 8 ∗
            savedCalleeSlots s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
            memRegion x.out 48 ∗
            pkBoxAt x.fut x.self x.id 0#8 ∗
            dirAt A.repAlloc x.self x.dir)) := by
      unfold F_drop; sep_ac_rfl
    rw [hpull, hrestk_dec]
    refine Entails.trans (sepConj_mono_left h24_name) ?_
    unfold F_dec2; exact Entails.of_eq (by sep_ac_rfl)
  refine sepWPp_conseq hprep_dec ?_
  apply sepWPp_seq_lscro (mid := lsmpl.base 597) hcrlm3
  wp_steps_sync_pool (lsmpl.base 597)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_dec2
  refine sepWPp_name_state_placed fun s4 hs4 => ?_
  have hs4_pc : s4.pc = lsmpl.base 597 := by
    rw [hs4]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs4_lr : s4.readReg64 Reg.lr = (blkPl_575).base + 160#64 := by
    rw [hs4]; simp only [wp_norm, arm64_norm, *]
  have hs4_run : s4.status = .Running := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_sp : s4.sp = s0.sp - 0xc0#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_tr : s4.trace = s0.trace := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x0 : s4.readReg64 .x0 = s0.sp - 0x78#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x1 : s4.readReg32 .x1 = x.id := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x19 : s4.readReg64 .x19 = x.fut := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x20 : s4.readReg64 .x20 = x.out := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x22 : s4.readReg64 .x22 = x.self := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x24 : s4.readReg64 .x24 = bytesCap := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x25 : s4.readReg64 .x25 = bytesPtr := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x26 : s4.readReg64 .x26 = okTagVec := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_x27 : s4.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length := by
    rw [hs4]; simp only [arm64_norm, *]
  have hs4_x28 : s4.readReg64 .x28 = s0.readReg64 .x28 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_fp : s4.readReg64 .x29 = s0.sp - 0x60#64 := by rw [hs4]; simp only [arm64_norm, *]
  have hs4_vregs : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
    rw [hs4]; simp only [arm64_norm, *]
  rw [← hs4] at hcrl_dec2 ⊢
  clear hs4
  refine pkrm_call_decimal_placed hDec
    { n := x.id, ret := s0.sp - 0x78#64 } st3 F_dec2
    hs4_pc hs4_run (spAligned_sub_c0 hsp_align hs4_sp) hs4_lr hcrl_dec2
    hs4_x0 hs4_x1 hfit3.seq_left
    (Entails.of_eq (by rw [hs4_sp]; sep_ac_rfl))
    fun sm4 evs3 hpcm4 hrunm4 hspm4 hcsm4 hcrlm4 htrm4 hevs3 => ?_
  rw [hs4_sp]
  let st4 := M.stepEvents evs3 st3
  have hfit4 : FitsEnv M lim st4 (PutEnv x.dir (keyName x.id) []) :=
    hfit3.seq_right hevs3
  rcases hcsm4 with
    ⟨hx19_4, hx20_4, _, hx22_4, _, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hfp_4, hvregs_4⟩
  have hsp_m4 : sm4.sp = s0.sp - 0xc0#64 := hspm4.trans hs4_sp
  have hsp_al4 : sm4.spAligned = true := spAligned_sub_c0 hsp_align hsp_m4
  have hx19_m4 : sm4.readReg64 .x19 = x.fut := hx19_4.trans hs4_x19
  have hx20_m4 : sm4.readReg64 .x20 = x.out := hx20_4.trans hs4_x20
  have hx22_m4 : sm4.readReg64 .x22 = x.self := hx22_4.trans hs4_x22
  have hx24_m4 : sm4.readReg64 .x24 = bytesCap := hx24_4.trans hs4_x24
  have hx25_m4 : sm4.readReg64 .x25 = bytesPtr := hx25_4.trans hs4_x25
  have hx26_m4 : sm4.readReg64 .x26 = okTagVec := hx26_4.trans hs4_x26
  have hx27_m4 : sm4.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length :=
    hx27_4.trans hs4_x27
  have hx28_m4 : sm4.readReg64 .x28 = s0.readReg64 .x28 := hx28_4.trans hs4_x28
  have hfp_m4 : sm4.readReg64 .x29 = s0.sp - 0x60#64 := hfp_4.trans hs4_fp
  have hvregs_m4 : calleeSavedVRegs sm4 = calleeSavedVRegs s0 := hvregs_4.trans hs4_vregs
  have htr_m4 : sm4.trace = s0.trace := htrm4.trans hs4_tr
  have hrestk_put :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - decStk) ∗
      stackAt (s0.sp - 0xc0#64) decStk =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - putStk) ∗
      stackAt (s0.sp - 0xc0#64) putStk := by
    rw [← subStack_split s0.sp hdec_le hmin_hi, subStack_split s0.sp hput_le hmin_hi]
  unfold F_dec2
  refine sepWPp_conseq
    (P' := ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
          (subMax decStk getStk putStk - decStk) ∗
        stackAt (s0.sp - 0xc0#64) decStk) ∗
      ((s0.sp - 0xa8#64) ↦₆₄ okTagVec) ∗
      ((s0.sp - 0xa0#64) ↦₆₄ bytesCap) ∗
      ((s0.sp - 0x98#64) ↦₆₄ bytesPtr) ∗
      vecU8 A.repAlloc (s0.sp - 0x78#64) (keyName x.id) ∗
      dirAt A.repAlloc x.self x.dir ∗
      A.pool lim st4 sm4 ∗
      ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
      memRegion (s0.sp - 0x88#64) 16 ∗
      ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
      memRegion (s0.sp - 0xb0#64) 8 ∗
      savedCalleeSlots s0 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
      memRegion x.out 48 ∗
      pkBoxAt x.fut x.self x.id 0#8))
    (Entails.of_eq (by unfold keyName; sep_ac_rfl)) ?_
  rw [hrestk_put]
  simp only [sepConj_assoc]
  apply sepWPp_seq_lscro (mid := lsmpl.base 542) hcrlm4
  wp_steps_sync_pool (lsmpl.base 542)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro hcrl_put
  refine sepWPp_name_state_placed fun s5 hs5 => ?_
  have hs5_pc : s5.pc = lsmpl.base 542 := by
    rw [hs5]; simp only [wp_norm, arm64_norm, *]; try bv_omega
  have hs5_lr : s5.readReg64 Reg.lr = (blkPl_575).base + 188#64 := by
    rw [hs5]; simp only [wp_norm, arm64_norm, *]
  have hs5_run : s5.status = .Running := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_sp : s5.sp = s0.sp - 0xc0#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_tr : s5.trace = s0.trace := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x0 : s5.readReg64 .x0 = x.self := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x1 : s5.readReg64 .x1 = s0.sp - 0x78#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x2 : s5.readReg64 .x2 = s0.sp - 0xa8#64 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x19 : s5.readReg64 .x19 = x.fut := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x20 : s5.readReg64 .x20 = x.out := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x24 : s5.readReg64 .x24 = bytesCap := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x25 : s5.readReg64 .x25 = bytesPtr := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x26 : s5.readReg64 .x26 = okTagVec := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_x27 : s5.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length := by
    rw [hs5]; simp only [arm64_norm, *]
  have hs5_x28 : s5.readReg64 .x28 = s0.readReg64 .x28 := by rw [hs5]; simp only [arm64_norm, *]
  have hs5_vregs : calleeSavedVRegs s5 = calleeSavedVRegs s0 := by
    rw [hs5]; simp only [arm64_norm, *]
  rw [← hs5] at hcrl_put ⊢
  clear hs5
  let F_put : SepProp :=
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - putStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
    memRegion x.out 48 ∗
    pkBoxAt x.fut x.self x.id 0#8
  refine pkrm_call_dirPut_placed hPut
    { self := x.self, dir := x.dir,
      nameV := s0.sp - 0x78#64, name := keyName x.id,
      bytesV := s0.sp - 0xa8#64, bytes := [] } st4 F_put
    hs5_pc hs5_run (spAligned_sub_c0 hsp_align hs5_sp) hs5_lr hcrl_put
    hs5_x0 hs5_x1 hs5_x2 hdchg hfit4
    (by
      rw [hs5_sp]
      have hemp_v := vecU8_empty_of_zero_one_zero A.repAlloc
        (s0.sp - 0xa8#64) (s0.sp - 0xa0#64) (s0.sp - 0x98#64) (by bv_omega) (by bv_omega)
      refine Entails.trans (Q :=
        (((s0.sp - 0xa8#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0xa0#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0x98#64) ↦₆₄ 0#64)) ∗
        (dirAt A.repAlloc x.self x.dir ∗ vecU8 A.repAlloc (s0.sp - 0x78#64) (keyName x.id) ∗
          stackAt (s0.sp - 0xc0#64) putStk ∗ A.pool lim st4 s5 ∗ F_put))
        (Entails.of_eq (by unfold F_put; sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hemp_v) ?_
      exact Entails.of_eq (by dsimp only; sep_ac_rfl))
    fun sm5 evs4 hpcm5 hrunm5 hspm5 hcsm5 hcrlm5 htrm5 hevs4 => ?_
  rw [hs5_sp]
  let st5 := M.stepEvents evs4 st4
  let evs_tot := evs1 ++ (evs2 ++ (evsDrop ++ (evs3 ++ evs4)))
  have hevs_tot : CliPkRemovePollEnv rd DecEnv GetEnv PutEnv s0.fs.files x evs_tot := by
    unfold CliPkRemovePollEnv
    refine SeqEnv.append hevs1 (SeqEnv.append hevs2 ?_)
    rw [← hgr.1]
    exact SeqEnv.append hfreeDrop (SeqEnv.append hevs3 hevs4)
  have hst_tot : M.stepEvents evs_tot st0 = st5 := by
    simp only [evs_tot, st5, st4, st3, st2, M.stepEvents_append]
  rcases hcsm5 with
    ⟨hx19_5, hx20_5, _, _, _, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, _, hvregs_5⟩
  have hsp_m5 : sm5.sp = s0.sp - 0xc0#64 := hspm5.trans hs5_sp
  have hx19_m5 : sm5.readReg64 .x19 = x.fut := hx19_5.trans hs5_x19
  have hx20_m5 : sm5.readReg64 .x20 = x.out := hx20_5.trans hs5_x20
  have hx24_m5 : sm5.readReg64 .x24 = bytesCap := hx24_5.trans hs5_x24
  have hx25_m5 : sm5.readReg64 .x25 = bytesPtr := hx25_5.trans hs5_x25
  have hx26_m5 : sm5.readReg64 .x26 = okTagVec := hx26_5.trans hs5_x26
  have hx27_m5 : sm5.readReg64 .x27 = BitVec.ofNat 64 (b0 :: bsRest).length :=
    hx27_5.trans hs5_x27
  have hx28_m5 : sm5.readReg64 .x28 = s0.readReg64 .x28 := hx28_5.trans hs5_x28
  have hvregs_m5 : calleeSavedVRegs sm5 = calleeSavedVRegs s0 := hvregs_5.trans hs5_vregs
  have htr_m5 : sm5.trace = s0.trace := htrm5.trans hs5_tr
  apply sepWPp_of_sepWP_final_placed
  have hrestk_ext :
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - putStk) ∗
      stackAt (s0.sp - 0xc0#64) putStk =
      memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
        (subMax decStk getStk putStk - extHookStack) ∗
      stackAt (s0.sp - 0xc0#64) extHookStack := by
    rw [← subStack_split s0.sp hput_le hmin_hi, subStack_split s0.sp hext_le hmin_hi]
  let F_end : SepProp :=
    dirAt A.repAlloc x.self (x.dir.put (keyName x.id) []) ∗
    memRegion (s0.sp - 0x78#64) 24 ∗
    memRegion (s0.sp - 0xa8#64) 24 ∗
    ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
    memRegion (s0.sp - 0x88#64) 16 ∗
    memRegion (s0.sp - 0xb0#64) 8 ∗
    memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
      (subMax decStk getStk putStk - extHookStack) ∗
    stackAt (s0.sp - 0xc0#64) extHookStack ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk)
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x okTagVec bytesCap bytesPtr
        (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 ∗ A.pool lim st5 sf ∗ F_end) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (pkRemovePollSpecPlaced rd pathOk A lim
          (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk).post (x, st0) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hres_f :
        (Except.ok (), x.dir.put (keyName x.id) []) =
          pkRemoveOf x.dir (keyName x.id) (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        sf.trace = s0.trace ∧
        CliPkRemovePollEnv rd DecEnv GetEnv PutEnv s0.fs.files x evs_tot :=
      ⟨by rw [← hgr.1]; rfl, htr_eq, hevs_tot⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    rw [← hst_tot]
    refine Entails.trans ?_
      (pkrm_post_entails_placed rd pathOk A lim
        (CliPkRemovePollEnv rd DecEnv GetEnv PutEnv) stk x st0 evs_tot s0 sf
        (.ok (), x.dir.put (keyName x.id) []) hres_f)
    refine Entails.trans ?_
      (finish_common_reassemble_placed A lim (M.stepEvents evs_tot st0) s0 sf x hstk hstk_hi
        (.ok (), x.dir.put (keyName x.id) []) q_sp0)
    have hok := pkRemoveOutAt_ok_reassemble A.repAlloc x.out bytesCap bytesPtr
      (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0
    have hslot := slot_a8_put_collapse s0.sp (BitVec.ofNat 64 (b0 :: bsRest).length)
    have hgrp :
        epilogueOut s0 x okTagVec bytesCap bytesPtr
          (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 ∗
          A.pool lim (M.stepEvents evs_tot st0) sf ∗ F_end =
        (((x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.out + 8#64) ↦₆₄ bytesCap) ∗ ((x.out + 0x10#64) ↦₆₄ bytesPtr) ∗
          ((x.out + 0x18#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
          ((x.out + 0x20#64) ↦₁₂₈ q_sp0)) ∗
        (memRegion (s0.sp - 0xa8#64) 24 ∗
          ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
          memRegion (s0.sp - 0x88#64) 16) ∗
        (dirAt A.repAlloc x.self (x.dir.put (keyName x.id) []) ∗
          memRegion (s0.sp - 0x78#64) 24 ∗
          ((s0.sp - 0xc0#64) ↦₁₂₈ q_sp0) ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk) ∗
          pkBoxAt x.fut x.self x.id 1#8 ∗
          A.pool lim (M.stepEvents evs_tot st0) sf)) := by
      unfold epilogueOut F_end okTagVec; sep_ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hok (sepConj_mono_left hslot)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hprep_end :
      ((dirAt A.repAlloc x.self (x.dir.put (keyName x.id) []) ∗
          memRegion (s0.sp - 0x78#64) 24 ∗ memRegion (s0.sp - 0xa8#64) 24 ∗
          stackAt (s0.sp - 0xc0#64) putStk ∗ A.pool lim st5 sm5) ∗ F_put) ⊢
      epiloguePre s0 x q_sp0 ∗ A.pool lim st5 sm5 ∗ F_end := by
    have hpull :
        ((dirAt A.repAlloc x.self (x.dir.put (keyName x.id) []) ∗
            memRegion (s0.sp - 0x78#64) 24 ∗ memRegion (s0.sp - 0xa8#64) 24 ∗
            stackAt (s0.sp - 0xc0#64) putStk ∗ A.pool lim st5 sm5) ∗ F_put) =
        ((memRegion (s0.sp - 0xc0#64 - BitVec.ofNat 64 (subMax decStk getStk putStk))
            (subMax decStk getStk putStk - putStk) ∗
          stackAt (s0.sp - 0xc0#64) putStk) ∗
        epiloguePre s0 x q_sp0 ∗
        A.pool lim st5 sm5 ∗
        (dirAt A.repAlloc x.self (x.dir.put (keyName x.id) []) ∗
          memRegion (s0.sp - 0x78#64) 24 ∗
          memRegion (s0.sp - 0xa8#64) 24 ∗
          ((s0.sp - 0x90#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bsRest).length) ∗
          memRegion (s0.sp - 0x88#64) 16 ∗
          memRegion (s0.sp - 0xb0#64) 8 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk decStk getStk putStk))) := by
      unfold F_put epiloguePre; sep_ac_rfl
    rw [hpull, hrestk_ext]
    unfold F_end; exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hprep_end ?_
  apply sepWP_seq_lscro (mid := (blkPl_575).base + 264#64) hcrlm5
  wp_steps_sync_pool ((blkPl_575).base + 264#64)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega) (by wp_norm_lhs)
  intro _hcrl_108
  refine hep x st5 s0 _ okTagVec bytesCap bytesPtr (BitVec.ofNat 64 (b0 :: bsRest).length) q_sp0 _
    F_end
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
    (Entails.of_eq (by sep_ac_rfl))
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.BranchesPlacedBudget
