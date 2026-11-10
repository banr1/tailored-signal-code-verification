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
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# `FdsGe3Closed`-Threaded Ok/Missing Branch and Cell Helpers for `get_pre_key::{closure#0}`

Proves the `FdsGe3Closed`-threaded `.missing` / `.found` branch helper `step_ok_240_placed_fd` and
the `FsFiles`-indexed `Dir::get` cell wrapper on Block `573` (`lsProg_573 H`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetAuxFd

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr
  (errTag okTagVec speAt speWord strRefAt vecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded
   sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGetGhost DirGhost PkAns PkPollGhost ReadRule dirAt getResultAt keyName pathOf pkAnsOf utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_573 blkPC_573 blkPl_573 lsProg_573)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
  (DirGetCellsGhost bind_sepWP_state dirGetPayload found_reassemble memRegion_16_cells
   memRegion_48_cells missing_reassemble pkBoxKeep pkDecPayload readErrHeap sp_sub_256_spAligned
   stackAt_sub_split vecU8BufRest vecU8Buf_eq_bytes_sep_rest)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (dirGetSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
  (CliPkGetPollEnv deallocBufCellsSpec dirGetCellsSpec dropSpeWordCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudgetFd
  (deallocBufCellsSpec_fd dropSpeWordCellsSpec_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAux
  (bytes_zero_elim_p)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAuxFd
  (pkEpiloguePost_fd pk_call_total_sepWP_lscro_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetFd
  (step_epilogue_348_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetAux
  (dirGetFsCellsSpec_p)
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

/-! ## 1. Branch 3/4 Helper: `.missing` (`+236 -> +240`) and `.found rec` (`+240` .. `+344` -> `+348`) -/

theorem step_ok_240_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (lsProg_573 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec_fd A lim calleeStk)))
    (hDropCells : subroutine_ok (lsProg_573 H) (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec_fd A lim calleeStk)))
    (ans : PkAns PreKeyRecord) (bytes : List (BitVec 8))
    (w1 w2 nCap nPtr nLen r26 r25 r28 r27 r21 qlo qhi u0 u1 u2 u3 k0 k1
      g0 g1 g2 g3 g4 g5 g6 : BitVec 64)
    (payload : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfds : FdsGe3Closed s.fs)
    (hpc : s.pc = (blkPl_573).base + bv% (240))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = r21)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = r25)
    (hx26 : s.readReg64 .x26 = r26)
    (hx27 : s.readReg64 .x27 = r27)
    (hx28 : s.readReg64 .x28 = r28)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns : ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)))
    (hevs : ∀ evs_free, FreeOnlyEvs evs_free →
      CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x (evs ++ evs_free))
    (hMode :
      (ans = .missing ∧ r26 = errTag ∧ payload = emp) ∨
      (∃ rec : PreKeyRecord, ans = .found rec ∧ r26 + 1#64 ≠ 0#64 ∧
        payload = pkDecPayload A.repAlloc (.ok rec) r26 r25 r28 r27 r21 qlo qhi))
    (hP : P ⊢
      pkBoxKeep x s0 ∗ payload ∗
        (w2 ↦ₛ bytes) ∗ vecU8BufRest A.repAlloc w1 w2 bytes ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) s ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost_fd rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk x st0 s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  suffices hjoin272 : ∀ (s1 : State) (P1 : SepProp) (evs1 : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl s1.mem →
      FdsGe3Closed s1.fs →
      s1.pc = (blkPl_573).base + bv% (272) →
      s1.status = .Running →
      s1.sp = s0.sp - 256#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = x.fut →
      s1.readReg64 .x20 = x.out →
      s1.readReg64 .x21 = r21 →
      s1.readReg64 .x22 = nPtr →
      s1.readReg64 .x25 = r25 →
      s1.readReg64 .x26 = r26 →
      s1.readReg64 .x27 = r27 →
      s1.readReg64 .x28 = r28 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (∀ evs_free, FreeOnlyEvs evs_free →
        CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x (evs1 ++ evs_free)) →
      (P1 ⊢ pkBoxKeep x s0 ∗ payload ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs1 st0) s1 ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) →
      SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s1 P1
        (pkEpiloguePost_fd rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk x st0 s0) by
    by_cases hw1 : w1 = 0#64
    · subst hw1
      refine bytes_zero_elim_p (ptr := w2) (bs := bytes)
        (Rest := pkBoxKeep x s0 ∗ payload ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
          dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) s ∗
          stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        (by sep_ac_rfl) ?_
      apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (272)) hcrl
      wp_steps_sync_pool ((blkPl_573).base + bv% (272))
      apply bind_sepWP_state; intro s1
      apply SepWP.done (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
      intro hcrl1
      have hfs1 : s1.fs = s.fs := by simp only [s1, wp_norm, arm64_norm]
      have hfds1 : FdsGe3Closed s1.fs := hfs1 ▸ hfds
      exact hjoin272 s1 _ evs hcrl1 hfds1
        (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        hevs
        (Entails.of_eq (by sep_ac_rfl))
    · have hw1_eq : (w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hw1
      have hw1_ne : (w1 != 0#64) = true := bne_iff_ne.mpr hw1
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply bind_sepWP_state; intro s_dl1
      apply SepWP.done (by simp only [s_dl1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_dl1, wp_norm, arm64_norm, *])
      intro hcrl1
      have hsp_dl1 : s_dl1.sp = s0.sp - 256#64 := by simp only [s_dl1, wp_norm, arm64_norm, hsp]
      have hal_dl1 : s_dl1.spAligned = true := sp_sub_256_spAligned hal0 hsp_dl1
      have hfs_dl1 : s_dl1.fs = s.fs := by simp only [s_dl1, wp_norm, arm64_norm]
      have hfds_dl1 : FdsGe3Closed s_dl1.fs := hfs_dl1 ▸ hfds
      refine pk_call_total_sepWP_lscro_fd
        ((w2, w1, bytes, s0.sp - 256#64), M.stepEvents evs st0)
        hDeallocCells hcrl1 hfds_dl1
        (by simp only [s_dl1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_dl1, wp_norm, arm64_norm, *])
        hal_dl1
        (by simp only [s_dl1, wp_norm, arm64_norm]; rfl)
        (F := pkBoxKeep x s0 ∗ payload ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
          dirAt A.repAlloc x.self x.dir ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        ?_ (hnext := ?_)
      · dsimp only [deallocBufCellsSpec]
        have hpure_dl1 :
            (s_dl1.readReg64 .x0 = w2 ∧ s_dl1.readReg64 .x1 = w1 ∧
              s_dl1.readReg64 .x2 = 1#64 ∧ s_dl1.sp = s0.sp - 256#64 ∧ w1 ≠ 0#64 ∧
              LsRetAddr624 (s_dl1.readReg64 .lr)) = True :=
          eq_true ⟨by simp only [s_dl1, wp_norm, arm64_norm, *],
            by simp only [s_dl1, wp_norm, arm64_norm, *],
            by simp only [s_dl1, wp_norm, arm64_norm],
            hsp_dl1, hw1,
            by simp (config := { decide := true }) [s_dl1, blkPl_573, wp_norm, arm64_norm, lsLen, *]⟩
        rw [hpure_dl1, ProofLib.pure_true, emp_sepConj]
        exact Entails.of_eq (by sep_ac_rfl)
      · rintro sf hcrl_sf hfds_sf hpc_sf hrun_sf hsp_sf
          ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, _, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf,
            hvregs_sf⟩
        dsimp only [deallocBufCellsSpec]
        rw [sepConj_assoc]
        refine SepWP.pure_elim fun htr_dl1 => ?_
        rw [← M.stepEvents_append]
        exact hjoin272 sf _ (evs ++ rustDeallocEvents w1.toNat 1) hcrl_sf hfds_sf
          (by simp only [wp_norm, arm64_norm, hpc_sf]; try bv_omega)
          hrun_sf
          (hsp_sf.trans hsp_dl1)
          (htr_dl1.trans (by simp only [s_dl1, wp_norm, arm64_norm, htr]))
          (hx19_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx19]))
          (hx20_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx20]))
          (hx21_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx21]))
          (hx22_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx22]))
          (hx25_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx25]))
          (hx26_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx26]))
          (hx27_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx27]))
          (hx28_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx28]))
          (hx29_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx29]))
          (hvregs_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hvregs]))
          (fun evs_free hf => by
            rw [List.append_assoc]
            exact hevs (rustDeallocEvents w1.toNat 1 ++ evs_free)
              (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 w1.toNat) hf))
          (Entails.of_eq (by sep_ac_rfl))
  clear hcrl hfds hpc hrun hsp hal htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hvregs
    hevs s evs
  intro s1 P1 evs1 hcrl1 hfds1 hpc1 hrun1 hsp1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h26_1 h27_1 h28_1
    h29_1 hv1 hevs1 hP1
  refine SepWP.weaken_pre hP1 ?_; clear hP1
  have hal1 : s1.spAligned = true := sp_sub_256_spAligned hal0 hsp1
  suffices hjoin292 : ∀ (s2 : State) (P2 : SepProp) (evs2 : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl s2.mem →
      FdsGe3Closed s2.fs →
      s2.pc = (blkPl_573).base + bv% (292) →
      s2.status = .Running →
      s2.sp = s0.sp - 256#64 →
      s2.trace = s0.trace →
      s2.readReg64 .x19 = x.fut →
      s2.readReg64 .x20 = x.out →
      s2.readReg64 .x21 = r21 →
      s2.readReg64 .x25 = r25 →
      s2.readReg64 .x26 = r26 →
      s2.readReg64 .x27 = r27 →
      s2.readReg64 .x28 = r28 →
      s2.readReg64 .x29 = s0.sp - 96#64 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      (∀ evs_free, FreeOnlyEvs evs_free →
        CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x (evs2 ++ evs_free)) →
      (P2 ⊢ pkBoxKeep x s0 ∗ payload ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs2 st0) s2 ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) →
      SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s2 P2
        (pkEpiloguePost_fd rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk x st0 s0) by
    by_cases hnCap : nCap = 0#64
    · subst hnCap
      refine bytes_zero_elim_p (ptr := nPtr) (bs := keyName x.id)
        (Rest := pkBoxKeep x s0 ∗ payload ∗
          dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs1 st0) s1 ∗
          stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        (by sep_ac_rfl) ?_
      apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (292)) hcrl1
      wp_steps_sync_pool ((blkPl_573).base + bv% (292))
      apply bind_sepWP_state; intro s2
      apply SepWP.done (by simp only [s2, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s2, wp_norm, arm64_norm, *])
      intro hcrl2
      have hfs2 : s2.fs = s1.fs := by simp only [s2, wp_norm, arm64_norm]
      have hfds2 : FdsGe3Closed s2.fs := hfs2 ▸ hfds1
      exact hjoin292 s2 _ evs1 hcrl2 hfds2
        (by simp only [s2, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        (by simp only [s2, wp_norm, arm64_norm, *])
        hevs1
        (Entails.of_eq (by sep_ac_rfl))
    · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
      have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply bind_sepWP_state; intro s_dl2
      apply SepWP.done (by simp only [s_dl2, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_dl2, wp_norm, arm64_norm, *])
      intro hcrl2
      have hsp_dl2 : s_dl2.sp = s0.sp - 256#64 := by simp only [s_dl2, wp_norm, arm64_norm, hsp1]
      have hal_dl2 : s_dl2.spAligned = true := sp_sub_256_spAligned hal0 hsp_dl2
      have hfs_dl2 : s_dl2.fs = s1.fs := by simp only [s_dl2, wp_norm, arm64_norm]
      have hfds_dl2 : FdsGe3Closed s_dl2.fs := hfs_dl2 ▸ hfds1
      refine pk_call_total_sepWP_lscro_fd
        ((nPtr, nCap, keyName x.id, s0.sp - 256#64), M.stepEvents evs1 st0)
        hDeallocCells hcrl2 hfds_dl2
        (by simp only [s_dl2, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_dl2, wp_norm, arm64_norm, *])
        hal_dl2
        (by simp only [s_dl2, wp_norm, arm64_norm]; rfl)
        (F := pkBoxKeep x s0 ∗ payload ∗
          dirAt A.repAlloc x.self x.dir ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
          ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
          ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
          ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
          ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
        ?_ (hnext := ?_)
      · dsimp only [deallocBufCellsSpec]
        have hpure_dl2 :
            (s_dl2.readReg64 .x0 = nPtr ∧ s_dl2.readReg64 .x1 = nCap ∧
              s_dl2.readReg64 .x2 = 1#64 ∧ s_dl2.sp = s0.sp - 256#64 ∧ nCap ≠ 0#64 ∧
              LsRetAddr624 (s_dl2.readReg64 .lr)) = True :=
          eq_true ⟨by simp only [s_dl2, wp_norm, arm64_norm, *],
            by simp only [s_dl2, wp_norm, arm64_norm, *],
            by simp only [s_dl2, wp_norm, arm64_norm],
            hsp_dl2, hnCap,
            by simp (config := { decide := true }) [s_dl2, blkPl_573, wp_norm, arm64_norm, lsLen, *]⟩
        rw [hpure_dl2, ProofLib.pure_true, emp_sepConj]
        exact Entails.of_eq (by sep_ac_rfl)
      · rintro sf hcrl_sf hfds_sf hpc_sf hrun_sf hsp_sf
          ⟨hx19_sf, hx20_sf, hx21_sf, _, _, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf,
            hvregs_sf⟩
        dsimp only [deallocBufCellsSpec]
        rw [sepConj_assoc]
        refine SepWP.pure_elim fun htr_dl2 => ?_
        rw [← M.stepEvents_append]
        exact hjoin292 sf _ (evs1 ++ rustDeallocEvents nCap.toNat 1) hcrl_sf hfds_sf
          (by simp only [wp_norm, arm64_norm, hpc_sf]; try bv_omega)
          hrun_sf
          (hsp_sf.trans hsp_dl2)
          (htr_dl2.trans (by simp only [s_dl2, wp_norm, arm64_norm, htr1]))
          (hx19_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h19_1]))
          (hx20_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h20_1]))
          (hx21_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h21_1]))
          (hx25_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h25_1]))
          (hx26_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h26_1]))
          (hx27_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h27_1]))
          (hx28_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h28_1]))
          (hx29_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h29_1]))
          (hvregs_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, hv1]))
          (fun evs_free hf => by
            rw [List.append_assoc]
            exact hevs1 (rustDeallocEvents nCap.toNat 1 ++ evs_free)
              (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 nCap.toNat) hf))
          (Entails.of_eq (by sep_ac_rfl))
  clear hcrl1 hfds1 hpc1 hrun1 hsp1 hal1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h26_1 h27_1 h28_1 h29_1
    hv1 hevs1 s1 evs1
  intro s2 P2 evs2 hcrl2 hfds2 hpc2 hrun2 hsp2 htr2 h19_2 h20_2 h21_2 h25_2 h26_2 h27_2 h28_2 h29_2
    hv2 hevs2 hP2
  refine SepWP.weaken_pre hP2 ?_; clear hP2
  have hal2 : s2.spAligned = true := sp_sub_256_spAligned hal0 hsp2
  have hspe13 : (0x800000000000000d#64 : BitVec 64) = speWord 13 := rfl
  rcases hMode with ⟨rfl, rfl, rfl⟩ | ⟨rec, rfl, hd0, rfl⟩
  · apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl2
    wp_steps_sync_pool ((blkPl_573).base + bv% (348))
    apply bind_sepWP_state; intro s_ep
    apply SepWP.done (by simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
    intro _hcrl_ep
    try rw [hspe13]
    have hfs_ep : s_ep.fs = s2.fs := by simp only [s_ep, wp_norm, arm64_norm]
    have hfds_ep : FdsGe3Closed s_ep.fs := hfs_ep ▸ hfds2
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    exact step_epilogue_348_placed_fd (A := A) (lim := lim)
      (DecEnv := DecEnv) (GetEnv := GetEnv) (PkDecEnv := PkDecEnv)
      (rd := rd) (pathOk := pathOk) (calleeStk := calleeStk)
      (x := x) (st0 := st0) (evs := evs2) (s0 := s0) (s := s_ep)
      .missing errTag (speWord 13) r28 r27 r21 u0 u1
      qlo qhi qlo qhi nCap nPtr nLen qlo qhi (speWord 13) g1 g2 g3 g4 g5 g6
      emp
      hfds_ep hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (by simpa only [List.append_nil] using hevs2 [] FreeOnlyEvs.nil)
      (by rw [sepConj_emp]; exact missing_reassemble A.repAlloc x.out r28 r27 r21 u0 u1)
      (Entails.of_eq (by sep_ac_rfl))
  · have hd0_eq : (r26 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hd0
    have hd0_ne : (r26 + 1#64 != 0#64) = true := bne_iff_ne.mpr hd0
    apply sepWP_seq_lscro (mid := lsmpl.base 553) hcrl2
    wp_steps_sync_pool (lsmpl.base 553)
    apply bind_sepWP_state; intro s_dr
    apply SepWP.done (by simp only [s_dr, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dr, wp_norm, arm64_norm, *])
    intro hcrl3
    try rw [hspe13]
    have hsp_dr : s_dr.sp = s0.sp - 256#64 := by simp only [s_dr, wp_norm, arm64_norm, hsp2]
    have hal_dr : s_dr.spAligned = true := sp_sub_256_spAligned hal0 hsp_dr
    have hfs_dr : s_dr.fs = s2.fs := by simp only [s_dr, wp_norm, arm64_norm]
    have hfds_dr : FdsGe3Closed s_dr.fs := hfs_dr ▸ hfds2
    refine pk_call_total_sepWP_lscro_fd
      ((s0.sp - 152#64, g1, g2, g3, g4, g5, s0.sp - 256#64), M.stepEvents evs2 st0)
      hDropCells hcrl3 hfds_dr
      (by simp only [s_dr, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dr, wp_norm, arm64_norm, *])
      hal_dr
      (by simp only [s_dr, wp_norm, arm64_norm]; rfl)
      (F := pkBoxKeep x s0 ∗
        pkDecPayload A.repAlloc (.ok rec) r26 r25 r28 r27 r21 qlo qhi ∗
        dirAt A.repAlloc x.self x.dir ∗
        ((s0.sp - 256#64) ↦₆₄ qlo) ∗ ((s0.sp - 248#64) ↦₆₄ qhi) ∗
        ((s0.sp - 240#64) ↦₆₄ qlo) ∗ ((s0.sp - 232#64) ↦₆₄ qhi) ∗
        ((s0.sp - 224#64) ↦₆₄ qlo) ∗ ((s0.sp - 216#64) ↦₆₄ qhi) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ qlo) ∗ ((s0.sp - 168#64) ↦₆₄ qhi) ∗
        ((s0.sp - 104#64) ↦₆₄ g6))
      ?_ (hnext := ?_)
    · dsimp only [dropSpeWordCellsSpec]
      try simp only [bv_sub_add_lit]
      have hpure_dr : (s_dr.readReg64 .x0 = s0.sp - 152#64 ∧ s_dr.sp = s0.sp - 256#64) = True :=
        eq_true ⟨by simp only [s_dr, wp_norm, arm64_norm, *], hsp_dr⟩
      rw [hpure_dr, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · rintro sf hcrl_sf hfds_sf hpc_sf hrun_sf hsp_sf
        ⟨hx19_sf, hx20_sf, hx21_sf, _, _, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf,
          hvregs_sf⟩
      dsimp only [dropSpeWordCellsSpec]
      try simp only [bv_sub_add_lit]
      simp only [sepExists_sepConj_left]
      refine SepWP.exists_elim fun m0 => SepWP.exists_elim fun m1 =>
        SepWP.exists_elim fun m2 => SepWP.exists_elim fun m3 =>
        SepWP.exists_elim fun m4 => SepWP.exists_elim fun m5 => ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun htr_dr => ?_
      have hsp_sf' : sf.sp = s0.sp - 256#64 := hsp_sf.trans hsp_dr
      have hal_sf : sf.spAligned = true := sp_sub_256_spAligned hal0 hsp_sf'
      have hx19_sf' : sf.readReg64 .x19 = x.fut :=
        hx19_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h19_2])
      have hx20_sf' : sf.readReg64 .x20 = x.out :=
        hx20_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h20_2])
      have hx21_sf' : sf.readReg64 .x21 = r21 :=
        hx21_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h21_2])
      have hx25_sf' : sf.readReg64 .x25 = r25 :=
        hx25_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h25_2])
      have hx26_sf' : sf.readReg64 .x26 = r26 :=
        hx26_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h26_2])
      have hx27_sf' : sf.readReg64 .x27 = r27 :=
        hx27_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h27_2])
      have hx28_sf' : sf.readReg64 .x28 = r28 :=
        hx28_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h28_2])
      have hx29_sf' : sf.readReg64 .x29 = s0.sp - 96#64 :=
        hx29_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, h29_2])
      have hvregs_sf' : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        hvregs_sf.trans (by simp only [s_dr, wp_norm, arm64_norm, hv2])
      have htr_sf' : sf.trace = s0.trace :=
        htr_dr.trans (by simp only [s_dr, wp_norm, arm64_norm, htr2])
      apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl_sf
      wp_steps_sync_pool ((blkPl_573).base + bv% (348))
      apply bind_sepWP_state; intro s_ep
      apply SepWP.done (by simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_ep, wp_norm, arm64_norm, *])
      intro _hcrl_ep
      have hfs_ep : s_ep.fs = sf.fs := by simp only [s_ep, wp_norm, arm64_norm]
      have hfds_ep : FdsGe3Closed s_ep.fs := hfs_ep ▸ hfds_sf
      have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
        simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
      exact step_epilogue_348_placed_fd (.found rec) r26 r25 r28 r27 r21 qlo qhi
        qlo qhi qlo qhi nCap nPtr nLen qlo qhi m0 m1 m2 m3 m4 m5 g6
        (pkDecPayload A.repAlloc (.ok rec) r26 r25 r28 r27 r21 qlo qhi)
        hfds_ep hpc_ep
        (by simp only [s_ep, wp_norm, arm64_norm, *])
        (by simp only [s_ep, wp_norm, arm64_norm, hsp_sf'])
        hal0
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        (by simp only [s_ep, s_dr, wp_norm, arm64_norm, *])
        ⟨hAns, by simp only [s_ep, s_dr, wp_norm, arm64_norm, *]⟩
        (by simpa only [List.append_nil] using hevs2 [] FreeOnlyEvs.nil)
        (found_reassemble A.repAlloc x.out rec r26 r25 r28 r27 r21 qlo qhi)
        (Entails.of_eq (by sep_ac_rfl))

/-! ## 2. `FdsGe3Closed`-Threaded `FsFiles`-Indexed `Dir::get` Cell Wrapper -/

private theorem sepExists_congr_p {α : Type} {f g : α → SepProp} (h : ∀ x, f x = g x) :
    (∃∗ x, f x) = (∃∗ x, g x) :=
  congrArg sepExists (funext h)

private theorem pure_true_eq_emp_p {P : Prop} (h : P) : (⌜P⌝ : SepProp) = emp := by
  rw [eq_true h]
  exact pure_true

private theorem vecU8_eq_words_sep_bytes_rest_p (A : RustAlloc) (v : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8 A v bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold vecU8
  apply sepExists_congr_p; intro cap
  apply sepExists_congr_p; intro ptr
  rw [vecU8At_eq_header_sep_buf, vecU8Buf_eq_bytes_sep_rest]
  dsimp only [vecHeader]
  sep_ac_rfl

def dirGetFsCellsSpec_p_fd {M : AllocCostModel} (F0 : FsFiles)
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DirGetCellsGhost × M.σ) :=
  withFdsGe3Closed (dirGetFsCellsSpec_p F0 rd pathOk A lim GetEnv calleeStk)

theorem dirGet_fs_cells_placed_ok_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F0 : FsFiles}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl (dirGetFsCellsSpec_p_fd F0 rd pathOk A lim GetEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨ret, self, dir, nameA, name, o0, o1, o2, o3, o4, o5, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [dirGetFsCellsSpec_p_fd] at hpre
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  simp only [dirGetFsCellsSpec_p, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hsf0, hx0, hx1, hx2, hx3, hfsp, hnlen, hplen, hpok, hfit⟩, hmem⟩
  subst hsf0 hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost × M.σ := (⟨ret, self, dir, nameA, name, false⟩, st)
  have hpre0 : s0.mem ⊨
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)).pre callG s0 ∗
      (stkRem ∗ R) := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG, CryptoVerification.SpqrV1.ChainProofs.bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, memRegion_48_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnlen, hplen, hpok, hfit⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hGet.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hfdsf, hq⟩
    dsimp only [dirGetFsCellsSpec_p_fd, withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    dsimp only [withLsCodeRoLoaded, dirGetSpecPlaced, dirGetFsCellsSpec_p, dirGetCellsSpec, callG,
      CryptoVerification.SpqrV1.ChainProofs.bytesAt] at hq ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, r, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdisj, hq⟩
    rcases r with ⟨⟩ | bs
    · dsimp only [getResultAt, speAt, strRefAt] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w4, ebs, hq⟩
      have hq' : sf.mem ⊨ vecU8 A.repAlloc (ret + 8#64) ebs ∗
          ((ret ↦₆₄ speWord 1) ∗ ((ret + 32#64) ↦₆₄ w4) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (w4 ↦ᵣ utf8 "read") ∗ dirAt A.repAlloc self dir ∗ (nameA ↦ₛ name) ∗
            stackAt s0.sp getStk ∗ A.pool lim (M.stepEvents evs st) sf ∗ (stkRem ∗ R)) := by
        convert hq using 1; sep_ac_rfl
      dsimp only [vecU8] at hq'
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq'
      rcases hq' with ⟨w1, w2, hq'⟩
      rw [vecU8At_eq_header_sep_buf] at hq'
      dsimp only [vecHeader] at hq'
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq'
      refine ⟨evs, .error (), speWord 1, w1, w2, BitVec.ofNat 64 ebs.length, w4,
        BitVec.ofNat 64 (utf8 "read").length, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload, readErrHeap]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
      refine ⟨ebs, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq'
      convert hq' using 1; sep_ac_rfl
    · dsimp only [getResultAt, vecResultAt] at hq
      rw [vecU8_eq_words_sep_bytes_rest_p A.repAlloc (ret + 8#64) bs] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w1, w2, hq⟩
      rw [memRegion_16_cells (ret + 32#64)] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w5, w4, hq⟩
      refine ⟨evs, .ok bs, okTagVec, w1, w2, BitVec.ofNat 64 bs.length, w4, w5, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp_p trivial, emp_sepConj]
      dsimp only [stkRem] at hq
      convert hq using 1; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.SymPlacedBudgetAuxFd
