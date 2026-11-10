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
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Relocatable Symbolic Execution of `get_pre_key::{closure#0}`

Proves budget-threaded `pkGetPollInner_placed_ok`, `pkGetPoll_placed_ok`, and
`pkGetPoll_placed_fs_ok` on Block `573` (`lsProg_573 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalTripleRatchetRepr
  (errTag okTagVec speAt speWord strRefAt vecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded TraceFsSound extract_withLsCodeRoLoaded
   sepWP_seq_lscro sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGetGhost DirGhost PkAns PkNameOk PkPollGhost PkSizeOk ReadRule
   dirAt getResultAt keyName pathOf pkAnsOf pkBoxAt pkGetAnsAt utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_573 blkPC_573 blkPl_573 lsProg_573)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
  (DirGetCellsGhost bind_sepWP_state cells_32_split cells_sub_12_96_eq cells_sub_2_176_eq
   cells_sub_3_200_eq cells_sub_6_256_eq cells_sub_7_152_eq dirGetPayload found_reassemble
   memRegion_16_cells memRegion_48_cells memRegion_bound_of_pointsTo64 missing_reassemble
   pkBoxKeep pkDecPayload pkPollSlack pkSavedRegs readErrHeap sp_sub_256_spAligned
   stackAt_pkPoll_frame stackAt_sub_split vecU8BufRest vecU8Buf_eq_bytes_sep_rest)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustDeallocEvents)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PreKeyDeserializeEnv RecordCodecLoopEnv preKeyDeserializePlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced decimalSpecPlaced dirGetSpecPlaced dropSpeWordSpecPlaced
   pkGetPollSpecOfPlaced pkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
  (CliPkGetPollEnv OptPkDecodeEnv deallocBufCellsSpec decimalCellsSpec dirGetCellsSpec
   dropSpeWordCellsSpec pkDecCellsSpec pkGetPollInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAux
  (bytes_zero_elim_p dealloc_buf_cells_placed_ok decimal_cells_placed_ok
   dropSpeWord_cells_placed_ok pkDec_cells_placed_ok pkEpiloguePost pkGetPoll_placed_of_inner
   pk_call_total_sepWP_lscro pk_call_total_sepWPp_lscro)
open CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers.CliPkGetPollNorm
  (calleeSavedVRegs_setMem_pre calleeSavedVRegs_setPC_pre calleeSavedVRegs_writeVReg128_zero
   cond_eq_adds64 cond_eq_addsPState64 cond_ne_adds64 cond_ne_addsPState64
   extractLsb_append_hi extractLsb_append_lo
   fs_setMem_pre fs_setPC_pre fs_setPState_pre fs_writeReg32_pre fs_writeReg64_pre
   readReg32_setMem_pre readReg32_setPC_pre readReg32_setPState_pre readReg32_writeVReg128_pre
   readReg64_setMem_pre readReg64_setPC_pre readReg64_setPState_pre
   readReg_setMem_pre readReg_setPC_pre readReg_setPState_pre
   readVReg128_setMem_pre readVReg128_setPC_pre readVReg128_setPState_pre
   readVReg128_writeReg32_pre readVReg128_writeReg64_pre
   sp_restore_256 sp_setMem_pre sp_setPC_pre sp_setPState_pre
   trace_setMem_pre trace_setPC_pre trace_setPState_pre trace_writeReg32_pre trace_writeReg64_pre
   zext32_trunc32)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudget
  (cliPkGetPollEnv_of_steps step_dec_err_152_placed step_epilogue_348_placed step_err_200_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetAux
  (bind_sepWPp_state_p dirGetFsCellsSpec_p dirGet_fs_cells_placed_ok sepWP_peek_err_tag_p
   sepWP_peek_ok_hd0_p sepWPp_exists_mid_p sepWPp_exists_right_p step_ok_240_placed)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_pre sp_setPState_pre
  readReg64_setPC_pre readReg64_setMem_pre readReg64_setPState_pre
  readReg32_setPC_pre readReg32_setMem_pre readReg32_setPState_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_pre readReg_setPState_pre
  readVReg128_setPC_pre readVReg128_setMem_pre readVReg128_setPState_pre
  readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre fs_writeReg64_pre fs_writeReg32_pre
  trace_setPC_pre trace_setMem_pre trace_setPState_pre trace_writeReg64_pre trace_writeReg32_pre
  calleeSavedVRegs_setPC_pre calleeSavedVRegs_setMem_pre calleeSavedVRegs_writeVReg128_zero
  extractLsb_append_lo extractLsb_append_hi
attribute [local arm64_norm, local wp_norm]
  zext32_trunc32 sp_restore_256
  cond_eq_adds64 cond_ne_adds64 cond_eq_addsPState64 cond_ne_addsPState64

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


/-! ## Main Symbolic Execution of Block `573` (`pkGetPollInner_placed_ok`, `pkGetPoll_placed_ok`, `pkGetPoll_placed_fs_ok`) -/

private theorem pkGetPollInner_sepWPp_of_pre [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_573 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_573 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok (lsProg_573 H) (lsmpl.base 65)
      (preKeyDeserializePlacedSpec A lim))
    (hDrop : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (dropSpeWordSpecPlaced A lim))
    (hFs : TraceFsSound (lsProg_573 H))
    (hle_dec : decStk ≤ calleeStk)
    (hle_get : getStk ≤ calleeStk)
    (hle_root : smallRootStack ≤ calleeStk)
    (hle_drop : dropSpeStackX ≤ calleeStk)
    (hle_hook : extHookStack ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs)
    (x : PkPollGhost) (st0 : M.σ) (Fr : SepProp) (s0 : State)
    (hpc0 : s0.pc = (blkPl_573).base)
    (hrun0 : s0.status = .Running)
    (hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (pkGetPollInnerSpec rd pathOk A lim DecEnv (GetEnv s0.fs.files) PkDecEnv calleeStk)).pre
        (x, st0) s0 ∗ Fr)
    (hal0 : s0.spAligned = true) :
    ∃ P : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp (lsProg_573 H) (s0.readReg64 Reg.lr) s0 P
        (pkEpiloguePost rd pathOk A lim DecEnv (GetEnv s0.fs.files) PkDecEnv calleeStk x st0 s0)
        (fun _ _ => False) := by
  obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre0
  dsimp only [pkGetPollInnerSpec] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx8, hname0, hsize0, hfit0⟩, hmem0⟩
  obtain ⟨hnlen, hplen, hpok⟩ := hname0
  have hnlen_bv : (BitVec.ofNat 64 (keyName x.id).length).toNat = (keyName x.id).length :=
    Nat.mod_eq_of_lt (by omega)
  have hwp : SepWPp (lsProg_573 H) (s0.readReg64 Reg.lr) s0
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 56 ∗ A.pool lim st0 s0 ∗
        stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32)
      (pkEpiloguePost rd pathOk A lim DecEnv (GetEnv s0.fs.files) PkDecEnv calleeStk x st0 s0)
      (fun _ _ => False) := by
    have hDeallocCells := dealloc_buf_cells_placed_ok (prog := lsProg_573 H)
      (calleeStk := calleeStk) hC hle_hook hhi
    have hDecimalCells := decimal_cells_placed_ok (calleeStk := calleeStk)
      hDecimal hFs hle_dec hhi
    have hGetCells := dirGet_fs_cells_placed_ok (F0 := s0.fs.files) (calleeStk := calleeStk)
      hGet hle_get hhi
    have hDecCells := pkDec_cells_placed_ok (calleeStk := calleeStk)
      hDec hle_root hhi hSub hSup
    have hDropCells := dropSpeWord_cells_placed_ok (calleeStk := calleeStk)
      hDrop hle_drop hhi
    clear hC hDecimal hGet hDec hDrop hFs
    have hfit_dec : FitsEnv M lim st0 (DecEnv x.id) := hfit0.seq_left
    refine SepWPp.weaken_pre
      (P' := ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 56 ∗ A.pool lim st0 s0 ∗
        stackAt (s0.sp - 256#64) calleeStk ∗ pkPollSlack s0.sp) ∗
        (cells (s0.sp - 256#64) 6 ∗ (cells (s0.sp - 200#64) 3 ∗
          (cells (s0.sp - 176#64) 2 ∗ (cells (s0.sp - 152#64) 7 ∗ cells (s0.sp - 96#64) 12)))))
      (by rw [cells_32_split]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    rw [cells_sub_6_256_eq]
    apply sepWPp_exists_mid_p; intro v
    apply sepWPp_exists_mid_p; intro v_1
    apply sepWPp_exists_mid_p; intro v_2
    apply sepWPp_exists_mid_p; intro v_3
    apply sepWPp_exists_mid_p; intro v_4
    apply sepWPp_exists_mid_p; intro v_5
    rw [← sepConj_assoc, cells_sub_3_200_eq]
    apply sepWPp_exists_mid_p; intro v_6
    apply sepWPp_exists_mid_p; intro v_7
    apply sepWPp_exists_mid_p; intro v_8
    rw [← sepConj_assoc, cells_sub_2_176_eq]
    apply sepWPp_exists_mid_p; intro v_9
    apply sepWPp_exists_mid_p; intro v_10
    rw [← sepConj_assoc, cells_sub_7_152_eq]
    apply sepWPp_exists_mid_p; intro v_11
    apply sepWPp_exists_mid_p; intro v_12
    apply sepWPp_exists_mid_p; intro v_13
    apply sepWPp_exists_mid_p; intro v_14
    apply sepWPp_exists_mid_p; intro v_15
    apply sepWPp_exists_mid_p; intro v_16
    apply sepWPp_exists_mid_p; intro v_17
    rw [← sepConj_assoc, cells_sub_12_96_eq]
    apply sepWPp_exists_right_p; intro v_18
    apply sepWPp_exists_right_p; intro v_19
    apply sepWPp_exists_right_p; intro v_20
    apply sepWPp_exists_right_p; intro v_21
    apply sepWPp_exists_right_p; intro v_22
    apply sepWPp_exists_right_p; intro v_23
    apply sepWPp_exists_right_p; intro v_24
    apply sepWPp_exists_right_p; intro v_25
    apply sepWPp_exists_right_p; intro v_26
    apply sepWPp_exists_right_p; intro v_27
    apply sepWPp_exists_right_p; intro v_28
    apply sepWPp_exists_right_p; intro v_29
    apply sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl0
    wp_steps_sync_pool (lsmpl.base 597)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state_p; intro s_dec
    have hsp_dec : s_dec.sp = s0.sp - 256#64 := by simp only [s_dec, wp_norm, arm64_norm]
    have hal_dec : s_dec.spAligned = true := sp_sub_256_spAligned hal0 hsp_dec
    refine pk_call_total_sepWPp_lscro
      ((x.id, s0.sp - 200#64, v_6, v_7, v_8, s0.sp - 256#64), st0)
      hDecimalCells hcrl1
      (by simp only [s_dec, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dec, wp_norm, arm64_norm, *])
      hal_dec
      (by simp only [s_dec, wp_norm, arm64_norm]; rfl)
      (F := pkBoxKeep x s0 ∗ dirAt A.repAlloc x.self x.dir ∗
        ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
        ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
        ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
        ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10) ∗
        ((s0.sp - 152#64) ↦₆₄ v_11) ∗ ((s0.sp - 144#64) ↦₆₄ v_12) ∗
        ((s0.sp - 136#64) ↦₆₄ v_13) ∗ ((s0.sp - 128#64) ↦₆₄ v_14) ∗
        ((s0.sp - 120#64) ↦₆₄ v_15) ∗ ((s0.sp - 112#64) ↦₆₄ v_16) ∗
        ((s0.sp - 104#64) ↦₆₄ v_17))
      ?_ (hnext := ?_)
    · dsimp only [decimalCellsSpec]
      try simp only [bv_sub_add_lit]
      have hpure_dec :
          (s_dec.readReg64 .x0 = s0.sp - 200#64 ∧
            s_dec.readReg32 .x1 = x.id ∧
            s_dec.sp = s0.sp - 256#64 ∧
            FitsEnv M lim st0 (DecEnv x.id)) = True :=
        eq_true ⟨by simp only [s_dec, wp_norm, arm64_norm, *],
          by simp only [s_dec, wp_norm, arm64_norm, *],
          hsp_dec, hfit_dec⟩
      rw [hpure_dec, ProofLib.pure_true, emp_sepConj]
      unfold pkBoxKeep pkSavedRegs
      exact Entails.of_eq (by sep_ac_rfl)
    · rintro s_ad hcrl_ad hpc_ad hrun_ad hsp_ad
        ⟨h19_ad, h20_ad, h21_ad, h22_ad, h23_ad, h24_ad, h25_ad, h26_ad, h27_ad, h28_ad, h29_ad,
          hvr_ad⟩
      dsimp only [decimalCellsSpec]
      try simp only [bv_sub_add_lit]
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun evsDec =>
        SepWPp.exists_elim fun nCap => SepWPp.exists_elim fun nPtr => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨htr_ad0, hfs_ad0, hevsDec⟩ => ?_
      have hfit_r1 := hfit0.seq_right hevsDec
      have hfit_get : FitsEnv M lim (M.stepEvents evsDec st0)
          (GetEnv s0.fs.files x.dir (keyName x.id)) :=
        hfit_r1.seq_left
      simp only [s_dec, wp_norm, arm64_norm] at hpc_ad hsp_ad h19_ad h20_ad h21_ad h22_ad h23_ad h24_ad
      simp only [s_dec, wp_norm, arm64_norm] at h25_ad h26_ad h27_ad h28_ad h29_ad hvr_ad htr_ad0 hfs_ad0
      have hsp_ad' : s_ad.sp = s0.sp - 256#64 := hsp_ad
      have hal_ad : s_ad.spAligned = true := sp_sub_256_spAligned hal0 hsp_ad'
      have htr_ad : s_ad.trace = s0.trace := htr_ad0
      have hfs_ad : s_ad.fs.files = s0.fs.files := hfs_ad0
      apply sepWPp_seq_lscro (mid := lsmpl.base 589) hcrl_ad
      wp_steps_sync_pool (lsmpl.base 589)
      apply SepWP.done (by simp only [s_dec, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_dec, wp_norm, arm64_norm, *])
      intro hcrl2
      apply bind_sepWPp_state_p; intro s_get
      have hsp_get : s_get.sp = s0.sp - 256#64 :=
        by simp only [s_get, s_dec, wp_norm, arm64_norm, *]
      have hal_get : s_get.spAligned = true := sp_sub_256_spAligned hal0 hsp_get
      have hfs_get : s_get.fs.files = s0.fs.files :=
        by simp only [s_get, wp_norm, arm64_norm, hfs_ad]
      refine pk_call_total_sepWPp_lscro
        ((s0.sp - 152#64, x.self, x.dir, nPtr, keyName x.id,
          v_11, v_12, v_13, v_14, v_15, v_16, s0.sp - 256#64),
          M.stepEvents evsDec st0)
        hGetCells hcrl2
        (by simp only [s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_get, s_dec, wp_norm, arm64_norm, *])
        hal_get
        (by simp only [s_get, wp_norm, arm64_norm]; rfl)
        (F := pkBoxKeep x s0 ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
          ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
          ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
          ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗
          ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10) ∗
          ((s0.sp - 104#64) ↦₆₄ v_17))
        ?_ (hnext := ?_)
      · dsimp only [dirGetFsCellsSpec_p]
        try simp only [bv_sub_add_lit]
        have hpure_get :
            (s_get.fs.files = s0.fs.files ∧
              s_get.readReg64 .x0 = s0.sp - 152#64 ∧
              s_get.readReg64 .x1 = x.self ∧
              s_get.readReg64 .x2 = nPtr ∧
              (s_get.readReg64 .x3).toNat = (keyName x.id).length ∧
              s_get.sp = s0.sp - 256#64 ∧
              (keyName x.id).length < 2 ^ 32 ∧
              x.dir.path.length < 2 ^ 32 ∧
              pathOk (pathOf x.dir.path (keyName x.id)) ∧
              FitsEnv M lim (M.stepEvents evsDec st0)
                (GetEnv s0.fs.files x.dir (keyName x.id))) = True :=
          eq_true ⟨hfs_get,
            by simp only [s_get, s_dec, wp_norm, arm64_norm, *],
            by simp only [s_get, s_dec, wp_norm, arm64_norm, *],
            by simp only [s_get, s_dec, wp_norm, arm64_norm, *],
            by simp only [s_get, s_dec, wp_norm, arm64_norm, *],
            hsp_get, hnlen, hplen, hpok, hfit_get⟩
        rw [hpure_get, ProofLib.pure_true, emp_sepConj]
        exact Entails.of_eq (by sep_ac_rfl)
      · rintro s_ag hcrl_ag hpc_ag hrun_ag hsp_ag
          ⟨h19_ag, h20_ag, h21_ag, h22_ag, h23_ag, h24_ag, h25_ag, h26_ag, h27_ag, h28_ag, h29_ag,
            hvr_ag⟩
        dsimp only [dirGetFsCellsSpec_p, dirGetCellsSpec]
        try simp only [bv_sub_add_lit]
        simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun evsGet =>
          SepWPp.exists_elim fun w_2 =>
          SepWPp.exists_elim fun w_3 => SepWPp.exists_elim fun w_4 =>
          SepWPp.exists_elim fun w_5 => SepWPp.exists_elim fun w_6 =>
          SepWPp.exists_elim fun w_7 => SepWPp.exists_elim fun w_8 => ?_
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hr_get, htr_ag0, hevsGet⟩ => ?_
        rw [← M.stepEvents_append]
        have hfit_r2 := hfit_r1.seq_right hevsGet
        rw [← M.stepEvents_append] at hfit_r2
        simp only [s_get, s_dec, wp_norm, arm64_norm,
          hsp_ad, h19_ad, h20_ad, h21_ad, h22_ad, h23_ad, h24_ad, h25_ad, h26_ad, h27_ad, h28_ad,
          h29_ad, hvr_ad, htr_ad0, hfs_ad0] at hpc_ag hsp_ag h19_ag h20_ag h21_ag h22_ag h23_ag h24_ag
        simp only [s_get, s_dec, wp_norm, arm64_norm,
          hsp_ad, h19_ad, h20_ad, h21_ad, h22_ad, h23_ad, h24_ad, h25_ad, h26_ad, h27_ad, h28_ad,
          h29_ad, hvr_ad, htr_ad0, hfs_ad0] at h25_ag h26_ag h27_ag h28_ag h29_ag hvr_ag htr_ag0
        have hsp_ag' : s_ag.sp = s0.sp - 256#64 := hsp_ag
        have hal_ag : s_ag.spAligned = true := sp_sub_256_spAligned hal0 hsp_ag'
        have htr_ag : s_ag.trace = s0.trace := htr_ag0
        have hget_post :
            w_2 = x.dir.get rd s0.fs.files (keyName x.id) ∧ s_ag.trace = s0.trace :=
          ⟨by rw [← hfs_get]; exact hr_get, htr_ag⟩
        refine SepWPp.weaken_pre
          (P' := dirGetPayload A.repAlloc w_2 w_3 w_4 w_5 w_6 w_7 w_8 ∗
            ((s0.sp - 152#64) ↦₆₄ w_3) ∗ ((s0.sp - 144#64) ↦₆₄ w_4) ∗
            ((s0.sp - 136#64) ↦₆₄ w_5) ∗ ((s0.sp - 128#64) ↦₆₄ w_6) ∗
            ((s0.sp - 120#64) ↦₆₄ w_7) ∗ ((s0.sp - 112#64) ↦₆₄ w_8) ∗
            ((s0.sp - 104#64) ↦₆₄ v_17) ∗
            (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
            pkBoxKeep x s0 ∗ dirAt A.repAlloc x.self x.dir ∗
            A.pool lim (M.stepEvents (evsDec ++ evsGet) st0) s_ag ∗
            stackAt (s0.sp - 256#64) calleeStk ∗
            ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
            ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
            ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
            ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗
            ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
            ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
          (Entails.of_eq (by sep_ac_rfl)) ?_
        rcases w_2 with ⟨⟩ | ⟨⟩ | ⟨b0, rest⟩
        · -- `r = .error ()`
          dsimp only [dirGetPayload]
          simp only [sepConj_assoc]
          refine SepWPp.pure_elim fun hw0 => ?_
          subst hw0
          apply sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (200)) hcrl_ag
          wp_steps_sync_pool ((blkPl_573).base + bv% (200))
          apply SepWP.done (by simp only [s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [s_get, s_dec, wp_norm, arm64_norm, *])
          intro hcrl_err
          apply SepWPp.of_sepWP_ret
          apply bind_sepWP_state; intro s_err
          have htr_err : s_err.trace = s_ag.trace := by simp only [s_err, wp_norm, arm64_norm]
          have hAns_err :
              (PkAns.readErr : PkAns PreKeyRecord) =
                  pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
                s_err.trace = s0.trace :=
            ⟨by rw [← hget_post.1]; rfl, htr_err.trans hget_post.2⟩
          have hpc_err : s_err.pc = (blkPl_573).base + bv% (200) := by
            simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega
          have hopt_err :
              OptPkDecodeEnv PkDecEnv (x.dir.get rd s0.fs.files (keyName x.id)) [] := by
            rw [← hget_post.1]; rfl
          refine step_err_200_placed hDeallocCells
            w_4 w_5 w_6 w_7 w_8 nCap nPtr (BitVec.ofNat 64 (keyName x.id).length)
            v v_1 v_2 v_3 v_4 v_5 v_9 v_10 v_17
            hcrl_err hpc_err
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            hal0
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            (by simp only [s_err, s_get, s_dec, wp_norm, arm64_norm, *])
            hAns_err
            (fun evs_free hf => by
              simpa only [List.append_nil] using
                cliPkGetPollEnv_of_steps hevsDec hevsGet hopt_err hf)
            (Entails.of_eq (by sep_ac_rfl))
        · -- `r = .ok []`
          have ⟨hget_eq, htr_sf1⟩ :
              x.dir.get rd s0.fs.files (keyName x.id) = .ok [] ∧ s_ag.trace = s0.trace :=
            ⟨hget_post.1.symm, hget_post.2⟩
          have hAns_miss :
              PkAns.missing =
                pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) := by
            rw [hget_eq]; rfl
          have hopt_miss :
              OptPkDecodeEnv PkDecEnv (x.dir.get rd s0.fs.files (keyName x.id)) [] := by
            rw [hget_eq]; rfl
          dsimp only [dirGetPayload]
          simp only [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hw0, hw3⟩ => ?_
          change w_6 = 0#64 at hw3
          subst hw0 hw3
          apply sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (240)) hcrl_ag
          wp_steps_sync_pool ((blkPl_573).base + bv% (240))
          apply SepWP.done (by simp only [s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [s_get, s_dec, wp_norm, arm64_norm, *])
          intro hcrl_miss
          apply SepWPp.of_sepWP_ret
          apply bind_sepWP_state; intro s_miss
          have hpc_miss : s_miss.pc = (blkPl_573).base + bv% (240) := by
            simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega
          have hm_run : s_miss.status = .Running :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_sp : s_miss.sp = s0.sp - 256#64 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_tr : s_miss.trace = s0.trace :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_19 : s_miss.readReg64 .x19 = x.fut :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_20 : s_miss.readReg64 .x20 = x.out :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_21 : s_miss.readReg64 .x21 = 0#64 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_22 : s_miss.readReg64 .x22 = nPtr :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_23 : s_miss.readReg64 .x23 = w_4 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_24 : s_miss.readReg64 .x24 = w_5 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_25 : s_miss.readReg64 .x25 = okTagVec :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_26 : s_miss.readReg64 .x26 = errTag := by
            simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]; rfl
          have hm_27 : s_miss.readReg64 .x27 = s0.sp - 152#64 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_28 : s_miss.readReg64 .x28 = s0.readReg64 .x28 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_29 : s_miss.readReg64 .x29 = s0.sp - 96#64 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          have hm_vr : calleeSavedVRegs s_miss = calleeSavedVRegs s0 :=
            by simp only [s_miss, s_get, s_dec, wp_norm, arm64_norm, *]
          refine step_ok_240_placed hDeallocCells hDropCells
            .missing []
            w_4 w_5 nCap nPtr (BitVec.ofNat 64 (keyName x.id).length)
            errTag okTagVec (s0.readReg64 .x28) (s0.sp - 152#64) 0#64
            v_4 v_5 v v_1 v_2 v_3 v_9 v_10
            okTagVec w_4 w_5 0#64 w_7 w_8 v_17
            emp
            hcrl_miss hpc_miss hm_run hm_sp hal0 hm_tr
            hm_19 hm_20 hm_21 hm_22 hm_23 hm_24 hm_25 hm_26 hm_27 hm_28 hm_29 hm_vr
            hAns_miss
            (fun evs_free hf => by
              simpa only [List.append_nil] using
                cliPkGetPollEnv_of_steps hevsDec hevsGet hopt_miss hf)
            (Or.inl ⟨rfl, rfl, rfl⟩)
            ?_
          rw [emp_sepConj]
          exact Entails.of_eq (by sep_ac_rfl)
        · -- `r = .ok (b0 :: rest)`
          have ⟨hget_eq, htr_sf1⟩ :
              x.dir.get rd s0.fs.files (keyName x.id) = .ok (b0 :: rest) ∧
                s_ag.trace = s0.trace :=
            ⟨hget_post.1.symm, hget_post.2⟩
          have hblen : (b0 :: rest).length < 2 ^ 32 := hsize0 (b0 :: rest) hget_eq
          have hpos : 0 < (b0 :: rest).length := by simp
          have hblen_bv : (BitVec.ofNat 64 (b0 :: rest).length).toNat = (b0 :: rest).length :=
            Nat.mod_eq_of_lt (by omega)
          have hblen_nz : BitVec.ofNat 64 (b0 :: rest).length ≠ 0#64 := by
            intro hz
            have h0 : (BitVec.ofNat 64 (b0 :: rest).length).toNat = 0 := congrArg BitVec.toNat hz
            omega
          have hblen_eq : (BitVec.ofNat 64 (b0 :: rest).length == 0#64) = false :=
            beq_eq_false_iff_ne.mpr hblen_nz
          have hblen_ne : (BitVec.ofNat 64 (b0 :: rest).length != 0#64) = true :=
            bne_iff_ne.mpr hblen_nz
          have hfit_dk : FitsEnv M lim (M.stepEvents (evsDec ++ evsGet) st0)
              (PkDecEnv (b0 :: rest)) := by
            have hfit_opt := hfit_r2.seq_left
            rwa [hget_eq] at hfit_opt
          dsimp only [dirGetPayload]
          simp only [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hw0, hw3⟩ => ?_
          subst hw0 hw3
          apply sepWPp_seq_lscro (mid := lsmpl.base 65) hcrl_ag
          wp_steps_sync_pool (lsmpl.base 65)
          apply SepWP.done (by simp only [s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [s_get, s_dec, wp_norm, arm64_norm, *])
          intro hcrl3
          apply bind_sepWPp_state_p; intro s_dk
          have hsp_dk : s_dk.sp = s0.sp - 256#64 :=
            by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *]
          have hal_dk : s_dk.spAligned = true := sp_sub_256_spAligned hal0 hsp_dk
          refine pk_call_total_sepWPp_lscro
            ((w_5, b0 :: rest, s0.sp - 152#64,
              okTagVec, w_4, w_5, BitVec.ofNat 64 (b0 :: rest).length, w_7, w_8, v_17,
              s0.sp - 256#64),
              M.stepEvents (evsDec ++ evsGet) st0)
            hDecCells hcrl3
            (by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
            hal_dk
            (by simp only [s_dk, wp_norm, arm64_norm]; rfl)
            (F := vecU8BufRest A.repAlloc w_4 w_5 (b0 :: rest) ∗
              (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
              pkBoxKeep x s0 ∗ dirAt A.repAlloc x.self x.dir ∗
              ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
              ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
              ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
              ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗
              ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
              ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
            ?_ (hnext := ?_)
          · dsimp only [pkDecCellsSpec]
            simp only [pointsToBytes_cons]
            try simp only [bv_sub_add_lit]
            have hpure_dk :
                (s_dk.readReg64 .x0 = w_5 ∧
                  (s_dk.readReg64 .x1).toNat = (b0 :: rest).length ∧
                  (b0 :: rest).length < 2 ^ 32 ∧
                  s_dk.readReg64 .x8 = s0.sp - 152#64 ∧
                  s_dk.sp = s0.sp - 256#64 ∧
                  FitsEnv M lim (M.stepEvents (evsDec ++ evsGet) st0)
                    (PkDecEnv (b0 :: rest))) = True :=
              eq_true ⟨by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *],
                by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *],
                hblen,
                by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *],
                hsp_dk, hfit_dk⟩
            rw [hpure_dk, ProofLib.pure_true, emp_sepConj]
            exact Entails.of_eq (by sep_ac_rfl)
          · rintro s_adk hcrl_adk hpc_adk hrun_adk hsp_adk
              ⟨h19_adk, h20_adk, h21_adk, h22_adk, h23_adk, h24_adk, h25_adk, h26_adk, h27_adk,
                h28_adk, h29_adk, hvr_adk⟩
            dsimp only [pkDecCellsSpec]
            try simp only [bv_sub_add_lit]
            simp only [sepExists_sepConj_left]
            refine SepWPp.exists_elim fun evsDk =>
              SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
              SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
              SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
              SepWPp.exists_elim fun d6 => ?_
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun ⟨htr_adk0, hevsDk⟩ => ?_
            rw [← M.stepEvents_append]
            simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm,
              hsp_ag, h19_ag, h20_ag, h21_ag, h22_ag, h23_ag, h24_ag, h25_ag, h26_ag, h27_ag,
              h28_ag, h29_ag, hvr_ag, htr_ag0] at hpc_adk hsp_adk h19_adk h20_adk h21_adk h22_adk h23_adk h24_adk
            simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm,
              hsp_ag, h19_ag, h20_ag, h21_ag, h22_ag, h23_ag, h24_ag, h25_ag, h26_ag, h27_ag,
              h28_ag, h29_ag, hvr_ag, htr_ag0] at h25_adk h26_adk h27_adk h28_adk h29_adk hvr_adk htr_adk0
            have hsp_adk' : s_adk.sp = s0.sp - 256#64 := hsp_adk
            have hal_adk : s_adk.spAligned = true := sp_sub_256_spAligned hal0 hsp_adk'
            have htr_adk : s_adk.trace = s0.trace := htr_adk0
            have hopt_dk :
                OptPkDecodeEnv PkDecEnv (x.dir.get rd s0.fs.files (keyName x.id)) evsDk := by
              rw [hget_eq]; exact hevsDk
            rcases hdec : PreKeyRecord.deserialize (b0 :: rest) with e | rec
            · apply sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (152)) hcrl_adk
              refine sepWP_peek_err_tag_p (A := A.repAlloc) (e := e)
                (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6)
                (Rest := ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
                  ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
                  ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗
                  ((s0.sp - 104#64) ↦₆₄ d6) ∗
                  (w_5 ↦ₛ (b0 :: rest)) ∗ vecU8BufRest A.repAlloc w_4 w_5 (b0 :: rest) ∗
                  (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
                  pkBoxKeep x s0 ∗ dirAt A.repAlloc x.self x.dir ∗
                  A.pool lim (M.stepEvents ((evsDec ++ evsGet) ++ evsDk) st0) s_adk ∗
                  stackAt (s0.sp - 256#64) calleeStk ∗
                  ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
                  ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
                  ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
                  ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗
                  ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
                  ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
                (by simp only [pointsToBytes_cons]; sep_ac_rfl) fun hd0_tag => ?_
              have hd0_eq : (d0 + 1#64 == 0#64) = true := by rw [hd0_tag]; rfl
              have hd0_ne : (d0 + 1#64 != 0#64) = false := by rw [hd0_tag]; rfl
              wp_steps_sync_pool ((blkPl_573).base + bv% (152))
              apply SepWP.done
                (by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega)
                (by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
              intro hcrl_de
              apply SepWPp.of_sepWP_ret
              apply bind_sepWP_state; intro s_de
              have hpc_de : s_de.pc = (blkPl_573).base + bv% (152) := by
                simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega
              have hAns_de :
                  PkAns.decodeErr e =
                    pkAnsOf PreKeyRecord.deserialize
                      (x.dir.get rd s0.fs.files (keyName x.id)) := by
                rw [hget_eq, pkAnsOf, hdec]
              refine step_dec_err_152_placed hDeallocCells
                e (b0 :: rest)
                w_4 w_5 nCap nPtr (BitVec.ofNat 64 (keyName x.id).length)
                d0 d1 d2 d3 d4 d5 d6
                v v_1 v_2 v_3 v_9 v_10
                hcrl_de hpc_de
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                hal0
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_de, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                hd0_tag hAns_de
                (fun evs_free hf => cliPkGetPollEnv_of_steps hevsDec hevsGet hopt_dk hf)
                (Entails.of_eq (by simp only [pointsToBytes_cons]; sep_ac_rfl))
            · apply sepWPp_seq_lscro (mid := (blkPl_573).base + bv% (240)) hcrl_adk
              refine sepWP_peek_ok_hd0_p (A := A.repAlloc) (rec := rec)
                (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6)
                (Rest := ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
                  ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
                  ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗
                  ((s0.sp - 104#64) ↦₆₄ d6) ∗
                  (w_5 ↦ₛ (b0 :: rest)) ∗ vecU8BufRest A.repAlloc w_4 w_5 (b0 :: rest) ∗
                  (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
                  pkBoxKeep x s0 ∗ dirAt A.repAlloc x.self x.dir ∗
                  A.pool lim (M.stepEvents ((evsDec ++ evsGet) ++ evsDk) st0) s_adk ∗
                  stackAt (s0.sp - 256#64) calleeStk ∗
                  ((s0.sp - 256#64) ↦₆₄ v) ∗ ((s0.sp - 248#64) ↦₆₄ v_1) ∗
                  ((s0.sp - 240#64) ↦₆₄ v_2) ∗ ((s0.sp - 232#64) ↦₆₄ v_3) ∗
                  ((s0.sp - 224#64) ↦₆₄ v_4) ∗ ((s0.sp - 216#64) ↦₆₄ v_5) ∗
                  ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗
                  ((s0.sp - 184#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
                  ((s0.sp - 176#64) ↦₆₄ v_9) ∗ ((s0.sp - 168#64) ↦₆₄ v_10))
                (by simp only [pointsToBytes_cons]; sep_ac_rfl) fun hd0 => ?_
              have hd0_eq : (d0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hd0
              have hd0_ne : (d0 + 1#64 != 0#64) = true := bne_iff_ne.mpr hd0
              wp_steps_sync_pool ((blkPl_573).base + bv% (240))
              apply SepWP.done
                (by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega)
                (by simp only [s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
              intro hcrl_ok
              apply SepWPp.of_sepWP_ret
              apply bind_sepWP_state; intro s_ok
              have hpc_ok : s_ok.pc = (blkPl_573).base + bv% (240) := by
                simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *]; try bv_omega
              have hAns_ok :
                  PkAns.found rec =
                    pkAnsOf PreKeyRecord.deserialize
                      (x.dir.get rd s0.fs.files (keyName x.id)) := by
                rw [hget_eq, pkAnsOf, hdec]
              refine step_ok_240_placed hDeallocCells hDropCells
                (.found rec) (b0 :: rest)
                w_4 w_5 nCap nPtr (BitVec.ofNat 64 (keyName x.id).length)
                d0 d1 d2 d3 d4 d5 d6
                v v_1 v_2 v_3 v_9 v_10
                d0 d1 d2 d3 d4 d5 d6
                (pkDecPayload A.repAlloc (.ok rec) d0 d1 d2 d3 d4 d5 d6)
                hcrl_ok hpc_ok
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                hal0
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                (by simp only [s_ok, s_dk, s_get, s_dec, wp_norm, arm64_norm, *])
                hAns_ok
                (fun evs_free hf => cliPkGetPollEnv_of_steps hevsDec hevsGet hopt_dk hf)
                (Or.inr ⟨rec, rfl, hd0, rfl⟩)
                (Entails.of_eq (by simp only [pointsToBytes_cons]; sep_ac_rfl))
  exact ⟨_, hmem0, hwp⟩

/-- Full symbolic proof of the inner specification `pkGetPollInnerSpec` on `lsProg_573 H`
under `[LibsignalPlacement]`. -/
theorem pkGetPollInner_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_573 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_573 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk))
    (hDec : subroutine_ok (lsProg_573 H) (lsmpl.base 65)
      (preKeyDeserializePlacedSpec A lim))
    (hDrop : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (dropSpeWordSpecPlaced A lim))
    (hFs : TraceFsSound (lsProg_573 H))
    (hhi : max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)) ≤ 2 ^ 64)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs) :
    subroutine_ok (lsProg_573 H) (blkPl_573).base
      (withLsCodeRoLoaded lsmpl
        (pkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv PkDecEnv
          (max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))))) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre0 hal0
  obtain ⟨P, hmP, hwp⟩ := pkGetPollInner_sepWPp_of_pre (GetEnv := fun _ => GetEnv)
    hC hDecimal hGet hDec hDrop hFs
    (by omega) (by omega) (by omega) (by omega) (by omega) hhi hSub hSup
    x st0 R s0 hpc0 hrun0 hpre0 hal0
  refine ⟨P, R, hmP, fun R' hm' hL => ?_⟩
  rcases hwp R' hm' hL with
    ⟨sf, hsteps,
      ⟨hpc_f, hrun_f, P_f, hm_f, hsp_f, hcs_f, hent_f⟩ |
      ⟨_, _, _, hfalse⟩ |
      hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, P_f, hm_f,
      ⟨fun hmfR => ?_, hsp_f, hcs_f⟩⟩⟩
    dsimp only [withLsCodeRoLoaded]
    exact Satisfies.mono (sepConj_mono_left hent_f) hmfR
  · exact hfalse.elim
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Outer `pkGetPollSpecPlaced` proof on `lsProg_573 H` for state-independent `GetEnv`. -/
theorem pkGetPoll_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_573 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_573 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk))
    (hDec : subroutine_ok (lsProg_573 H) (lsmpl.base 65)
      (preKeyDeserializePlacedSpec A lim))
    (hDrop : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (dropSpeWordSpecPlaced A lim))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs) :
    subroutine_ok (lsProg_573 H) (blkPl_573).base
      (pkGetPollSpecPlaced rd pathOk A lim
        (CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd) stk) :=
  pkGetPoll_placed_of_inner
    (calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack)))
    (fun hhi => pkGetPollInner_placed_ok hC hDecimal hGet hDec hDrop hFs hhi hSub hSup)
    hstk

/-- Direct `pkGetPollSpecPlaced` proof on `lsProg_573 H` accepting an arbitrary `FsFiles`-indexed
`GetEnv` in `dirGetSpecPlaced`. -/
theorem pkGetPoll_placed_fs_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_573 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_573 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok (lsProg_573 H) (lsmpl.base 65)
      (preKeyDeserializePlacedSpec A lim))
    (hDrop : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (dropSpeWordSpecPlaced A lim))
    (hFs : TraceFsSound (lsProg_573 H))
    (hstk : 0x100 + max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
      ≤ stk)
    (hSub : ∀ bs evs, RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs → PkDecEnv bs evs)
    (hSup : ∀ bs evs, PreKeyDeserializeEnv bs.length evs → PkDecEnv bs evs) :
    subroutine_ok (lsProg_573 H) (blkPl_573).base
      (pkGetPollSpecPlaced rd pathOk A lim
        (fun F0 x => CliPkGetPollEnv DecEnv (GetEnv F0) PkDecEnv rd F0 x) stk) := by
  set calleeStk := max (max decStk getStk) (max smallRootStack (max dropSpeStackX extHookStack))
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre0 hal0
  unfold pkGetPollSpecPlaced pkGetPollSpecOfPlaced at hpre0
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre0
  dsimp only [] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx8, hname, hsize, hfit⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 13#64) 3 ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 56 ∗ A.pool lim st0 s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 256 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
    stackAt_pkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 13#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 256))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (pkGetPollInnerSpec rd pathOk A lim DecEnv (GetEnv s0.fs.files) PkDecEnv calleeStk)).pre
        (x, st0) s0 ∗ (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [pkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hsize, hfit⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; sep_ac_rfl
  obtain ⟨P, hmP, hwp⟩ := pkGetPollInner_sepWPp_of_pre (GetEnv := GetEnv)
    hC hDecimal hGet hDec hDrop hFs
    (by omega) (by omega) (by omega) (by omega) (by omega) hcal_hi hSub hSup
    x st0 (F_extra ∗ R) s0 hpc0 hrun0 hpre_in hal0
  refine ⟨P, F_extra ∗ R, hmP, fun R' hm' hL => ?_⟩
  rcases hwp R' hm' hL with
    ⟨sf, hsteps,
      ⟨hpc_f, hrun_f, P_f, hm_f, hsp_f, hcs_f, hent_f⟩ |
      ⟨_, _, _, hfalse⟩ |
      hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, P_f, hm_f,
      ⟨fun hmf_Fr => ?_, hsp_f, hcs_f⟩⟩⟩
    have hq := Satisfies.mono (sepConj_mono_left hent_f) hmf_Fr
    dsimp only [withLsCodeRoLoaded, pkGetPollInnerSpec, pkGetPollSpecPlaced,
      pkGetPollSpecOfPlaced, pkGetAnsAt, pkBoxAt] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
      stackAt_pkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · exact hfalse.elim
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudget
