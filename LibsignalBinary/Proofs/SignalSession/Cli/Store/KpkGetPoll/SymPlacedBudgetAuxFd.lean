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
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LastResortPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# `FdsGe3Closed`-Threaded Relocatable `one_time` Empty-File Cleanup Helpers for `KpkGetPoll`

Proves the `withFdsGe3Closed`-threaded `one_time` empty-file cleanup (`+268`, `+180`) on
Block `576` (`lsProg_576 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudgetAuxFd

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded TraceFsSound sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkPollGhost PkNameOk PkSizeOk ReadRule dirAt keyName pkAnsOf)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_576 blkPC_576 blkPl_576 lsProg_576)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
  (KpkScratch bind_sepWPp_state fsInv_of_eq kpkSavedRegs kpkScratchAt kpkSlack3 slot7At slotDecAt
   slotFp90At slotRetHeadAt slotRetTailAt slotSp40At slotSp70At sp_sub_432_spAligned
   vecU8Buf_zero_entails_emp words11At)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers.CliKpkGetPollNorm
  (extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre
   zext32_trunc32)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkLoopEnv decodeKyberPreKeyPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (CliKpkGetPollEnv KpkPassEnv deallocVecBufCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudgetFd
  (deallocVecBuf_cells_placed_ok_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.EpiloguePlacedBudgetFd
  (KpkExitPost_fd kpk_call_total_lscro_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LastResortPlacedBudgetFd
  (step_last_resort_placed_fd)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi zext32_trunc32
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

/-! ## `one_time` empty-file cleanup (`+268`, `+180`) with `FdsGe3Closed` -/

structure KpkCalleeDepsPlaced_fd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (decStk getStk : Nat) : Prop where
  dec : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
    (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk))
  get : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
    (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
  decode : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
    (withFdsGe3Closed (decodeKyberPreKeyPlacedSpec A lim))

theorem step_ot_free_name_next_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDeps : KpkCalleeDepsPlaced_fd A lim DecEnv GetEnv H rd pathOk decStk getStk)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_dec : decStk ≤ calleeStk)
    (hle_get : getStk ≤ calleeStk)
    (hle_root : smallRootStack ≤ calleeStk)
    (hle_hook : extHookStack ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (x : KpkPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    {s0 s : State}
    (sc : KpkScratch) (nPtr : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (hn2 : PkNameOk pathOk x.kg.lastResort x.id)
    (hs2 : PkSizeOk rd s0.fs.files x.kg.lastResort x.id)
    (hmiss1 : pkAnsOf KyberPreKeyRecord.deserialize
      (x.kg.oneTime.get rd s0.fs.files (keyName x.id)) = .missing)
    (hevs1_free : ∀ evsF, FreeOnlyEvs evsF →
      KpkPassEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
        rd s0.fs.files x.kg.oneTime x.id (evsPre ++ evsF))
    (hfit0 : FitsEnv M lim st0
      (CliKpkGetPollEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
        rd s0.fs.files x))
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsInv s0.fs.files s0.trace s)
    (hfds : FdsGe3Closed s.fs)
    (hpc : s.pc = (blkPl_576).base + 268#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx25 : s.readReg64 .x25 = x.id.zeroExtend 64) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evsPre st0) s ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost_fd rd pathOk A lim DecEnv
        (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv calleeStk x st0 s0)
      Qp := by
  by_cases hnCap : sc.dec0 = 0#64
  · have hdrop : vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ⊢ emp := by
      rw [hnCap]; exact vecU8Buf_zero_entails_emp A.repAlloc nPtr (keyName x.id)
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left hdrop) (Entails.of_eq (emp_sepConj _))) ?_
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply sepWPp_seq_lscro (mid := (blkPl_576).base + 288#64) hcrl
    dsimp only [kpkScratchAt, slotDecAt]
    rw [hnCap]
    wp_steps_sync_pool ((blkPl_576).base + 288#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s1
    have hfs1 : FsInv s0.fs.files s0.trace s1 :=
      fsInv_of_eq hfs (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm])
    have hfds1 : FdsGe3Closed s1.fs := by
      have hfs_eq : s1.fs = s.fs := by simp only [s1, arm64_norm]
      exact hfs_eq ▸ hfds
    have hevs1 : KpkPassEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
        rd s0.fs.files x.kg.oneTime x.id evsPre := by
      simpa only [List.append_nil] using hevs1_free [] FreeOnlyEvs.nil
    have hfit_lr : FitsEnv M lim (M.stepEvents evsPre st0)
        (KpkPassEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
          rd s0.fs.files x.kg.lastResort x.id) := by
      unfold CliKpkGetPollEnv at hfit0
      rw [hmiss1] at hfit0
      exact hfit0.seq_right hevs1
    refine SepWPp.weaken_pre ?_
      (step_last_resort_placed_fd hC hDeps.dec hDeps.get hDeps.decode hFs
        hle_dec hle_get hle_root hle_hook hhi hSub hSup x st0 evsPre sc
        u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hn2 hs2 hmiss1 hevs1 hfit_lr hal0 hcrl1 hfs1 hfds1
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, htr])
        (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *]))
    dsimp only [kpkScratchAt, slotDecAt]
    rw [hnCap]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hn_beq : (sc.dec0 == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hn_bne : (sc.dec0 != 0#64) = true := bne_iff_ne.mpr hnCap
    have _ := And.intro hn_beq hn_bne
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    dsimp only [kpkScratchAt, slotDecAt]
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dl
    have hsp_dl : s_dl.sp = s0.sp - 432#64 := by simp only [s_dl, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_432_spAligned hal0 hsp_dl
    have htr_dl : s_dl.trace = s0.trace := by simp only [s_dl, arm64_norm, htr]
    have hfs_dl : FsInv s0.fs.files s0.trace s_dl :=
      fsInv_of_eq hfs (by simp only [s_dl, arm64_norm]) (by simp only [s_dl, arm64_norm])
    have hfds_dl : FdsGe3Closed s_dl.fs := by
      have hfs_eq : s_dl.fs = s.fs := by simp only [s_dl, arm64_norm]
      exact hfs_eq ▸ hfds
    have hdealloc := deallocVecBuf_cells_placed_ok_fd (prog := lsProg_576 H)
      (F0 := s0.fs.files) (T0 := s0.trace) hC hFs hle_hook hhi (by decide)
    refine kpk_call_total_lscro_fd
      ((sc.dec0, nPtr, keyName x.id, s0.sp - 432#64), M.stepEvents evsPre st0)
      hdealloc hcrl1 hfds_dl
      (by simp only [s_dl, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dl, arm64_norm, *])
      hal_dl
      (ret_pc := (blkPl_576).base + 288#64)
      (by simp only [s_dl, wp_norm, arm64_norm])
      (F := words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [deallocVecBufCellsSpec, kpkScratchAt, slotDecAt]
      have hpure_dl :
          (FsInv s0.fs.files s0.trace s_dl ∧ sc.dec0 ≠ 0#64 ∧
            s_dl.readReg64 .x0 = nPtr ∧ s_dl.readReg64 .x1 = sc.dec0 ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 432#64 ∧
            LsRetAddr624 (s_dl.readReg64 .lr)) = True :=
        eq_true ⟨hfs_dl, hnCap,
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm],
          hsp_dl,
          by rw [show s_dl.readReg64 .lr = (blkPl_576).base + 288#64 by
               simp only [s_dl, wp_norm, arm64_norm]]
             exact lsRetAddr624_blockPlacement_base_add 576 288#64 (by decide) (by decide)⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after hcrl2 hfds2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [deallocVecBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hfs2, htr2⟩ => ?_
      rw [← M.stepEvents_append]
      have hevs1 : KpkPassEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
          rd s0.fs.files x.kg.oneTime x.id (evsPre ++ rustDeallocEvents sc.dec0.toNat 1) :=
        hevs1_free _ (FreeOnlyEvs.singleton 1 sc.dec0.toNat)
      have hfit_lr : FitsEnv M lim
          (M.stepEvents (evsPre ++ rustDeallocEvents sc.dec0.toNat 1) st0)
          (KpkPassEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
            rd s0.fs.files x.kg.lastResort x.id) := by
        unfold CliKpkGetPollEnv at hfit0
        rw [hmiss1] at hfit0
        exact hfit0.seq_right hevs1
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (step_last_resort_placed_fd hC hDeps.dec hDeps.get hDeps.decode hFs
          hle_dec hle_get hle_root hle_hook hhi hSub hSup
          x st0 (evsPre ++ rustDeallocEvents sc.dec0.toNat 1) sc
          u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hn2 hs2 hmiss1 hevs1 hfit_lr hal0 hcrl2 hfs2 hfds2
          hpc2 hrun2 (hsp2.trans hsp_dl) (htr2.trans htr_dl)
          (hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [s_dl, calleeSavedVRegs, arm64_norm]; exact hvregs))
          (hcsp2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx29]))
          (hcsp2.1.trans (by simp only [s_dl, arm64_norm, hx19]))
          (hcsp2.2.1.trans (by simp only [s_dl, arm64_norm, hx20]))
          (hcsp2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx24]))
          (hcsp2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx25])))

theorem step_ot_empty_next_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hDeps : KpkCalleeDepsPlaced_fd A lim DecEnv GetEnv H rd pathOk decStk getStk)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_dec : decStk ≤ calleeStk)
    (hle_get : getStk ≤ calleeStk)
    (hle_root : smallRootStack ≤ calleeStk)
    (hle_hook : extHookStack ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (x : KpkPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    {s0 s : State}
    (sc : KpkScratch) (nPtr bCap bPtr : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (hn2 : PkNameOk pathOk x.kg.lastResort x.id)
    (hs2 : PkSizeOk rd s0.fs.files x.kg.lastResort x.id)
    (hmiss1 : pkAnsOf KyberPreKeyRecord.deserialize
      (x.kg.oneTime.get rd s0.fs.files (keyName x.id)) = .missing)
    (hevs1_free : ∀ evsF, FreeOnlyEvs evsF →
      KpkPassEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
        rd s0.fs.files x.kg.oneTime x.id (evsPre ++ evsF))
    (hfit0 : FitsEnv M lim st0
      (CliKpkGetPollEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
        rd s0.fs.files x))
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsInv s0.fs.files s0.trace s)
    (hfds : FdsGe3Closed s.fs)
    (hpc : s.pc = (blkPl_576).base + 180#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx1 : s.readReg64 .x1 = bCap)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hx22 : s.readReg64 .x22 = bPtr)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx25 : s.readReg64 .x25 = x.id.zeroExtend 64) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (vecU8Buf A.repAlloc bCap bPtr [] ∗
        vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evsPre st0) s ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost_fd rd pathOk A lim DecEnv
        (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv calleeStk x st0 s0)
      Qp := by
  let sc1 : KpkScratch :=
    { sc with
      sp08 := s.readReg64 .x9,
      sp40_0 := sc.sp70_0, sp40_1 := sc.sp70_1,
      sp40_2 := sc.sp70_2, sp40_3 := sc.sp70_3,
      sp40_4 := sc.sp70_4, sp40_5 := sc.sp70_5,
      fp90_0 := sc.sp70_0, fp90_1 := sc.sp70_1,
      fp90_2 := sc.sp70_2, fp90_3 := sc.sp70_3,
      fp90_4 := sc.sp70_4, fp90_5 := sc.sp70_5 }
  have sameSlots :
      slotSp70At s0.sp sc1 = slotSp70At s0.sp sc ∧
      slotDecAt s0.sp sc1 = slotDecAt s0.sp sc ∧
      slotRetHeadAt s0.sp sc1 = slotRetHeadAt s0.sp sc ∧
      slotRetTailAt s0.sp sc1 = slotRetTailAt s0.sp sc :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
  let _ := hal
  by_cases hbCap : bCap = 0#64
  · subst hbCap
    have hdrop : vecU8Buf A.repAlloc 0#64 bPtr [] ⊢ emp :=
      vecU8Buf_zero_entails_emp A.repAlloc bPtr []
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left hdrop) (Entails.of_eq (emp_sepConj _))) ?_
    apply sepWPp_seq_lscro (mid := (blkPl_576).base + 268#64) hcrl
    dsimp only [kpkScratchAt, slot7At, slotSp40At, slotSp70At, slotFp90At]
    wp_steps_sync_pool ((blkPl_576).base + 268#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s1
    have hfs1 : FsInv s0.fs.files s0.trace s1 :=
      fsInv_of_eq hfs (by simp only [s1, arm64_norm]) (by simp only [s1, arm64_norm])
    have hfds1 : FdsGe3Closed s1.fs := by
      have hfs_eq : s1.fs = s.fs := by simp only [s1, arm64_norm]
      exact hfs_eq ▸ hfds
    refine SepWPp.weaken_pre ?_
      (step_ot_free_name_next_placed_fd hC hDeps hFs
        hle_dec hle_get hle_root hle_hook hhi hSub hSup x st0 evsPre sc1 nPtr
        u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hn2 hs2 hmiss1 hevs1_free hfit0 hal0 hcrl1 hfs1 hfds1
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, htr])
        (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *]))
    dsimp only [kpkScratchAt]
    rw [sameSlots.1, sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2]
    dsimp only [slot7At, slotSp40At, slotSp70At, slotFp90At, sc1]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hb_beq : (bCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbCap
    have hb_bne : (bCap != 0#64) = true := bne_iff_ne.mpr hbCap
    have _ := And.intro hb_beq hb_bne
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    dsimp only [kpkScratchAt, slot7At, slotSp40At, slotSp70At, slotFp90At]
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dl
    have hsp_dl : s_dl.sp = s0.sp - 432#64 := by simp only [s_dl, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_432_spAligned hal0 hsp_dl
    have htr_dl : s_dl.trace = s0.trace := by simp only [s_dl, arm64_norm, htr]
    have hfs_dl : FsInv s0.fs.files s0.trace s_dl :=
      fsInv_of_eq hfs (by simp only [s_dl, arm64_norm]) (by simp only [s_dl, arm64_norm])
    have hfds_dl : FdsGe3Closed s_dl.fs := by
      have hfs_eq : s_dl.fs = s.fs := by simp only [s_dl, arm64_norm]
      exact hfs_eq ▸ hfds
    have hdealloc := deallocVecBuf_cells_placed_ok_fd (prog := lsProg_576 H)
      (F0 := s0.fs.files) (T0 := s0.trace) hC hFs hle_hook hhi (by decide)
    refine kpk_call_total_lscro_fd
      ((bCap, bPtr, [], s0.sp - 432#64), M.stepEvents evsPre st0)
      hdealloc hcrl1 hfds_dl
      (by simp only [s_dl, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dl, arm64_norm, *])
      hal_dl
      (ret_pc := (blkPl_576).base + 268#64)
      (by simp only [s_dl, wp_norm, arm64_norm])
      (F := vecU8Buf A.repAlloc sc1.dec0 nPtr (keyName x.id) ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc1 ∗ kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [deallocVecBufCellsSpec, kpkScratchAt]
      rw [sameSlots.1, sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2]
      dsimp only [slot7At, slotSp40At, slotSp70At, slotFp90At, sc1]
      have hpure_dl :
          (FsInv s0.fs.files s0.trace s_dl ∧ bCap ≠ 0#64 ∧
            s_dl.readReg64 .x0 = bPtr ∧ s_dl.readReg64 .x1 = bCap ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 432#64 ∧
            LsRetAddr624 (s_dl.readReg64 .lr)) = True :=
        eq_true ⟨hfs_dl, hbCap,
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm],
          hsp_dl,
          by rw [show s_dl.readReg64 .lr = (blkPl_576).base + 268#64 by
               simp only [s_dl, wp_norm, arm64_norm]]
             exact lsRetAddr624_blockPlacement_base_add 576 268#64 (by decide) (by decide)⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after hcrl2 hfds2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [deallocVecBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hfs2, htr2⟩ => ?_
      rw [← M.stepEvents_append]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (step_ot_free_name_next_placed_fd hC hDeps hFs
          hle_dec hle_get hle_root hle_hook hhi hSub hSup
          x st0 (evsPre ++ rustDeallocEvents bCap.toNat 1) sc1 nPtr
          u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hn2 hs2 hmiss1
          (fun evsF hF => by
            rw [List.append_assoc]
            exact hevs1_free _ ((FreeOnlyEvs.singleton 1 bCap.toNat).append hF))
          hfit0 hal0 hcrl2 hfs2 hfds2
          hpc2 hrun2 (hsp2.trans hsp_dl) (htr2.trans htr_dl)
          (hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [s_dl, calleeSavedVRegs, arm64_norm]; exact hvregs))
          (hcsp2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx29]))
          (hcsp2.1.trans (by simp only [s_dl, arm64_norm, hx19]))
          (hcsp2.2.1.trans (by simp only [s_dl, arm64_norm, hx20]))
          (hcsp2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx21]))
          (hcsp2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx24]))
          (hcsp2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx25])))

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudgetAuxFd
