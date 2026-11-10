/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded `IdentityFiles::get_local_registration_id::{closure#0}` (`[LibsignalPlacement]`, Block `568`)

Provides two-sided `withFdsGe3Closed` (`*_fd`) and pre-only `FdsGe3Closed` (`*_preFd`) contracts
for `IdentityFiles::get_local_registration_id::{closure#0}` (Block `568`) under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack withStack)
open CryptoVerification.SignalSession
  (CliHooks lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdGhost ReadRule dirAt pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (blkLib_eq_568 blkPC_568 blkPl_568 lsProg_568)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (IdOwnPollGhostPlaced idOwnFutBoxAtPlaced satisfies_withLsCodeRoLoaded_pre
   stk_sub_ge_base stk_sub_ge_dirGet)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll
  (cells_14_reg getResultAt_err_sp_112 getResultAt_ok_sp_112 len_bv_ne_four_of_ne
   match_regId_ne_4 out_48_reg_split out_reg_err_malformed_fold out_reg_err_read_fold
   out_reg_ok_fold regCalleeStk sp_112_err_fold_48 sp_112_ok_fold_48)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll.RegNorm
  (awc_okTagVec_two awc_speWord1_two cap_reconstruct_norm fs_setMem_pre fs_setPC_pre
   fs_setPState_pre fs_writeReg32_pre fs_writeReg64_pre fs_writeReg_pre okTagVec_eq_neg2
   readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre readVReg128_setMem_pre
   readVReg128_setMem_setPC_pre readVReg128_setPC_pre readVReg128_setPState_pre
   readVReg128_writeReg32_pre readVReg128_writeReg64_pre readVReg128_writeReg_pre
   sp_setMem_setPC_pre sp_setPC_pre speWord_one_eq trace_writeReg32_pre trace_writeReg_pre)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon
  (idRegIdFileNameSym idRegIdOutAtPlaced_eq malformedFileStrSym memRegion_14_split_8_6
   rodata_regId_and_malformed_placed utf8_regId_length
   write_14_overlap_done write_14_overlap_length write_14_overlap_mid)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs (idRegIdOutAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
  (cap_ne_zero_of_cons memRegion_bound_of_pointsTo64 stackAt_sub_split vecU8BufRest)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro shim_keepsFs_lscro_of_fs
   subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdHelpersBudget
  (alloc14CellsSpec shimCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (CliIdRegIdPollEnv OptRegIdMalformedEnv alloc14At_cells_placed_ok shimAt_cells_vm_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudget
  (deallocAt_cells_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd
  (deallocAt_cells_placed_ok_fd dirGetRoFsCellsSpec_fd dirGetRoFs_cells_placed_ok_fd
   extract_withFdsGe3Closed_post)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced dirGetSpecPlaced idRegIdPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.CalleesBudget (deallocVecBufSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (AllocContractsFsPlaced.toAllocContractsX allocNoOomWithStack_lscro_of_budget alloc_lscro_of_cli)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)

section Placed

local elab "erase_hkdf_sp_norm%" : command =>
  Lean.Elab.Command.liftTermElabM do
    if let some ext ← Lean.Meta.getSimpExtension? `arm64_norm then
      for n in [
        `CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
        `CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
        `CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
        `CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
      ] do
        let s := (ext.getState (← Lean.getEnv)).eraseCore (.decl n)
        Lean.modifyEnv fun env => ext.modifyState env fun _ => s

erase_hkdf_sp_norm%

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local wp_norm]
  sp_setPC_pre sp_setMem_setPC_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre
  trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre
  cap_reconstruct_norm speWord_one_eq okTagVec_eq_neg2
  awc_speWord1_two awc_okTagVec_two truncate32_zeroExtend64

attribute [local arm64_norm]
  sp_setPC_pre sp_setMem_setPC_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre
  trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre
  cap_reconstruct_norm speWord_one_eq okTagVec_eq_neg2
  awc_speWord1_two awc_okTagVec_two truncate32_zeroExtend64

attribute [local irreducible] Program.fetch Program.externAt? FitsEnv FitsEvents

/-! ## `.keepsFs` Cell-Oriented Callee Wrappers -/

theorem shimAt_cells_vm_keepsFs_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (shimCellsSpec calleeStk)).keepsFs) := by
  have hShim := shim_keepsFs_lscro_of_fs (callerProg := prog) hC hle hhi hi
  refine subroutine_ok.of_codeLoaded fun fsp R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [Spec.keepsFs] at hpre
  simp only [withVmPreserved, shimCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfsp, hmem⟩
  subst hfsp
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec calleeStk).keepsFs).pre () s0 ∗ R := by
    refine satisfies_lscro_pre hcrl0 ?_
    dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    rw [emp_sepConj]
    exact hmem
  refine hShim.mono_outcome () R s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
      withVmPreserved, shimCellsSpec] at hq ⊢
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.keepsFs, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem shimAt_cells_keepsFs_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl (shimCellsSpec calleeStk).keepsFs) := by
  refine subroutine_ok_mono (shimAt_cells_vm_keepsFs_placed_ok hC hi hle hhi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withLsCodeRoLoaded, Spec.keepsFs, withVmPreserved] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  rcases hq with ⟨hfs, hq⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact ⟨hfs, hq.2⟩

theorem alloc14At_cells_keepsFs_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (alloc14CellsSpec M A lim calleeStk).keepsFs) := by
  have hAlloc := allocNoOomWithStack_lscro_of_budget (alloc_lscro_of_cli (callerProg := prog) hC hi)
  refine subroutine_ok.of_codeLoaded fun ⟨fsp, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [Spec.keepsFs] at hpre
  simp only [alloc14CellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp, hfit, hlr⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  have hlay : RustLayoutOk 14 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (rustAllocNoOomSpecWithStack M A lim false extHookStack)).pre
        (14, 1, st) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl0 ?_
    dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by rw [hx0]; rfl, by rw [hx1]; rfl, hlay, hfit, hlr⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hAlloc.mono_outcome (14, 1, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustAllocNoOomSpecWithStack,
      rustCliAllocNoOomSpecWithStack, alloc14CellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hpres, hnz, _hmod⟩, hq⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    refine ⟨hpres.1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hnz, hpres.2.1⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
      rustCliAllocNoOomSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, rustAllocNoOomSpecWithStack,
      rustCliAllocNoOomSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack,
      withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem out_reg_err_malformed_fold_budget {M : AllocCostModel}
    (A : RustCliAllocBudget M) (out buf o32 o40 : BitVec 64)
    (bs14 : List (BitVec 8))
    (hbuf : buf ≠ 0#64) (hlen14 : bs14.length = 14) :
    (out ↦₆₄ 0x8000000000000001#64) ∗
      ((out + 8#64) ↦₃₂ 14#32) ∗ ((out + 12#64) ↦₃₂ 0#32) ∗
      ((out + 16#64) ↦₆₄ buf) ∗ ((out + 24#64) ↦₆₄ 14#64) ∗
      A.live buf 14 1 ∗ (buf ↦ₛ bs14) ∗
      ((out + 32#64) ↦₆₄ o32) ∗ ((out + 40#64) ↦₆₄ o40) ⊢
    idRegIdOutAt A.repAlloc out (.error ()) :=
  out_reg_err_malformed_fold A.repAlloc out buf o32 o40 bs14 hbuf hlen14

private theorem subroutine_ok_lscro_withFdsGe3Closed_of_lscro_keepsFs {α : Type}
    {pl : MultiPlacement} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl spec.keepsFs)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (withFdsGe3Closed spec)) :=
  subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
    (subroutine_ok_mono h
      (fun _ _ _ hp => by dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hp ⊢; exact hp)
      (fun _ _ _ _ hq => by dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hq ⊢; exact hq))

/-! ## Parametric Post-FS Inner Specification and Symbolic Execution -/

private def withFsPred {α : Type} (FsPost : FsState → Prop) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => ⌜FsPost s.fs⌝ ∗ spec.pre x s
    post := fun x s0 sf => ⌜FsPost sf.fs⌝ ∗ spec.post x s0 sf }

private theorem subroutine_ok_lscro_withFsPred_true {α : Type} {pl : MultiPlacement}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl (withFsPred (fun _ => True) spec)) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hp
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [withFsPred] at hpre
      rwa [pure_true, emp_sepConj] at hpre)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCodeRoLoaded, withFsPred] at hq ⊢
      rwa [pure_true, emp_sepConj])

private def regPostPoolFs {M : AllocCostModel} (FsPost : FsState → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (Env : List AllocEvent → Prop) (out : BitVec 64)
    (expected : Except Unit (BitVec 32)) (s0 sf : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ∃∗ ans : Except Unit (BitVec 32),
    ⌜ans = expected ∧ sf.trace = s0.trace ∧ FsPost sf.fs ∧ Env evs⌝ ∗
      idRegIdOutAt A.repAlloc out ans ∗ A.pool lim (M.stepEvents evs st) sf

private theorem regPostPoolFs_intro {M : AllocCostModel} (FsPost : FsState → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st st_cur : M.σ)
    (Env : List AllocEvent → Prop) (evs : List AllocEvent) (out : BitVec 64)
    (expected ans : Except Unit (BitVec 32)) (s0 sf : State)
    (hst : st_cur = M.stepEvents evs st)
    (hpure : ans = expected ∧ sf.trace = s0.trace ∧ FsPost sf.fs ∧ Env evs) :
    idRegIdOutAt A.repAlloc out ans ∗ A.pool lim st_cur sf ⊢
      regPostPoolFs FsPost A lim st Env out expected s0 sf := by
  subst hst
  have htrue : ((ans = expected ∧ sf.trace = s0.trace ∧ FsPost sf.fs ∧ Env evs) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  unfold regPostPoolFs
  refine Entails.sepExists_right evs (Entails.sepExists_right ans ?_)
  rw [htrue, pure_true, emp_sepConj]
  exact Entails.refl _

private theorem focus_regPostPoolFs {M : AllocCostModel} (FsPost : FsState → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st st_cur : M.σ)
    (Env : List AllocEvent → Prop) (evs : List AllocEvent) (out : BitVec 64)
    (expected ans : Except Unit (BitVec 32)) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : P = (idRegIdOutAt A.repAlloc out ans ∗ A.pool lim st_cur s_ret) ∗ R)
    (hst : st_cur = M.stepEvents evs st)
    (hpure : ans = expected ∧ s_ret.trace = s0.trace ∧ FsPost s_ret.fs ∧ Env evs)
    (hnext : SepWP prog ret_pc s_ret
      (regPostPoolFs FsPost A lim st Env out expected s0 s_ret ∗ R) post oom) :
    SepWP prog ret_pc s_ret P post oom :=
  SepWP.focus_weaken
    (regPostPoolFs_intro FsPost A lim st st_cur Env evs out expected ans s0 s_ret hst hpure)
    (hf := hf) hnext

private def cliIdRegIdPollInnerPlacedSpecFs [LibsignalPlacement] {M : AllocCostModel}
    (FsPost : FsState → Prop) (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (w0 wTail : BitVec 64) (calleeStk : Nat) :
    Spec (IdOwnPollGhostPlaced × M.σ) where
  pre := fun (x, st) s =>
    ⌜FdsGe3Closed s.fs ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "registration-id")) ∧
      FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
      (lsρ idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      memRegion x.out 48 ∗ A.pool lim st s ∗
      stackAt (s.sp - 112#64) calleeStk ∗ cells (s.sp - 112#64) 14
  post := fun (x, st) s0 sf =>
    regPostPoolFs FsPost A lim st (PollEnv s0.fs.files x) x.out
        ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) s0 sf ∗
      (lsρ idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      stackAt (s0.sp - 112#64) calleeStk ∗ cells (s0.sp - 112#64) 14

private def cliIdRegIdPollExpandedPlacedSpecFs [LibsignalPlacement] {M : AllocCostModel}
    (FsPost : FsState → Prop) (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (w0 wTail : BitVec 64) (calleeStk : Nat) :
    Spec (IdOwnPollGhostPlaced × M.σ) where
  pre := fun (x, st) s =>
    ⌜FdsGe3Closed s.fs ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "registration-id")) ∧
      FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
      (lsρ idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      memRegion x.out 48 ∗ A.pool lim st s ∗
      stackAt (s.sp - 112#64) calleeStk ∗
      (memRegion (s.sp - 112#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s.sp - 64#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s.sp - 56#64) ↦₆₄ s30) ∗
        (∃∗ s23 : BitVec 64, (s.sp - 48#64) ↦₆₄ s23) ∗
        (∃∗ sPad : BitVec 64, (s.sp - 40#64) ↦₆₄ sPad) ∗
        (∃∗ s22 : BitVec 64, (s.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s.sp - 8#64) ↦₆₄ s19))
  post := fun (x, st) s0 sf =>
    regPostPoolFs FsPost A lim st (PollEnv s0.fs.files x) x.out
        ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) s0 sf ∗
      (lsρ idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      stackAt (s0.sp - 112#64) calleeStk ∗
      (memRegion (s0.sp - 112#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s0.sp - 64#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s0.sp - 56#64) ↦₆₄ s30) ∗
        (∃∗ s23 : BitVec 64, (s0.sp - 48#64) ↦₆₄ s23) ∗
        (∃∗ sPad : BitVec 64, (s0.sp - 40#64) ↦₆₄ sPad) ∗
        (∃∗ s22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s19))

private theorem cliIdRegIdPollExpandedPlacedSpecFs_eq [LibsignalPlacement] {M : AllocCostModel}
    (FsPost : FsState → Prop) (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (w0 wTail : BitVec 64) (calleeStk : Nat) :
    cliIdRegIdPollExpandedPlacedSpecFs FsPost rd pathOk A lim PollEnv w0 wTail calleeStk =
      cliIdRegIdPollInnerPlacedSpecFs FsPost rd pathOk A lim PollEnv w0 wTail calleeStk := by
  unfold cliIdRegIdPollExpandedPlacedSpecFs cliIdRegIdPollInnerPlacedSpecFs
  congr 1
  · funext ⟨x, st⟩ s; rw [cells_14_reg s.sp]
  · funext ⟨x, st⟩ s0 sf; rw [cells_14_reg s0.sp]

set_option pp.deepTerms false in
set_option pp.maxSteps 1000000 in
set_option maxHeartbeats 1600000 in
private theorem idRegIdPollInner_fsPost_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {FsPost : FsState → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {w0 wTail : BitVec 64} {getStk : Nat}
    (himp : ∀ fs, FdsGe3Closed fs → FsPost fs)
    (hGetCells : subroutine_ok (lsProg_568 H) (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetRoFsCellsSpec_fd rd pathOk A lim GetEnv (regCalleeStk getStk))))
    (hDeallocCells : subroutine_ok (lsProg_568 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl
        (withFsPred FsPost (deallocVecBufSpec A lim (regCalleeStk getStk)))))
    (hShimCells : subroutine_ok (lsProg_568 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl
        (withFsPred FsPost (withVmPreserved (shimCellsSpec (regCalleeStk getStk))))))
    (hAllocCells : subroutine_ok (lsProg_568 H) (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl
        (withFsPred FsPost (alloc14CellsSpec M A lim (regCalleeStk getStk))))) :
    subroutine_ok (lsProg_568 H) (blkPl_568).base
      (withLsCodeRoLoaded lsmpl
        (cliIdRegIdPollInnerPlacedSpecFs FsPost rd pathOk A lim (CliIdRegIdPollEnv GetEnv rd)
          w0 wTail (regCalleeStk getStk))) := by
  rw [← cliIdRegIdPollExpandedPlacedSpecFs_eq]
  dsimp only [dirGetRoFsCellsSpec_fd, withFdsGe3Closed, withFsPred]
    at hGetCells hDeallocCells hShimCells hAllocCells
  dsimp only [lsProg_568, ite_true] at hGetCells hDeallocCells hShimCells hAllocCells ⊢
  change subroutine_ok ((blkPC_568).rebase (blkPl_568).base H) (blkPl_568).base _
  dsimp only [withLsCodeRoLoaded]
  simp (config := { maxSteps := 2000000 }) only [cliIdRegIdPollExpandedPlacedSpecFs,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init xs s0
  obtain ⟨x, st⟩ := xs
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfds0 : FdsGe3Closed s0.fs := by assumption
  have hfit0 : FitsEnv M lim st (CliIdRegIdPollEnv GetEnv rd s0.fs.files x) := by assumption
  have hfit_get : FitsEnv M lim st (GetEnv s0.fs.files x.own (utf8 "registration-id")) :=
    CliIdRegIdPollEnv.fits_get hfit0
  have hname_len : (utf8 "registration-id").length = 15 := utf8_regId_length
  have hname_lt : (utf8 "registration-id").length < 2 ^ 32 := by
    rw [utf8_regId_length]; decide
  apply sepWP_seq_lscro (mid := lsmpl.base 589) hcrl0
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro hGetCells hcrl1
    ((s0.sp - 112#64, x.self, x.own,
      lsρ idRegIdFileNameSym, utf8 "registration-id", s0.sp - 112#64), st)
  have hfds_sf : FdsGe3Closed sf.fs := by
    simpa only [wp_norm, arm64_norm] using ‹FdsGe3Closed sf.fs›
  have hfs_sf : FsPost sf.fs := himp sf.fs hfds_sf
  have hget_evs : GetEnv s0.fs.files x.own (utf8 "registration-id") w := by
    simpa only [wp_norm, arm64_norm] using ‹GetEnv _ x.own (utf8 "registration-id") w›
  have h_reg0 : sf.sp = s0.sp - 112#64 ∧
      sf.readReg64 (.gpr 19#5) = x.fut ∧
      sf.readReg64 (.gpr 20#5) = x.out ∧
      sf.readReg64 (.gpr 29#5) = s0.sp - 64#64 :=
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  rcases h_reg0 with ⟨_, _, _, _⟩
  cases w_1 with
  | error u =>
    cases u
    have hget_err : .error () = x.own.get rd s0.fs.files (utf8 "registration-id") ∧
        sf.trace = s0.trace :=
      ⟨by simpa only [wp_norm, arm64_norm] using
            ‹(.error () : Except Unit (List (BitVec 8))) = _›,
       by simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›⟩
    have hans_err : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files = .error () := by
      unfold IdGhost.regId
      rw [← hget_err.1]
      rfl
    apply sepWP_seg_ls_vm (Q := (blkPC_568).rebase (blkPl_568).base (hooksException H))
      blkLib_eq_568 (mid := s0.readReg64 Reg.lr)
    intro _m_strip
    apply SepWP.focus_rw (getResultAt_err_sp_112 A.repAlloc s0.sp)
    wp_pull_exists
    apply SepWP.focus_rw (out_48_reg_split x.out)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_weaken (sp_112_err_fold_48 s0.sp _ _ _ _ _ _ _)
    apply SepWP.focus_weaken (out_reg_err_read_fold A.repAlloc x.out _ _ _ _)
    refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    refine focus_regPostPoolFs FsPost A lim st (M.stepEvents w st)
      (CliIdRegIdPollEnv GetEnv rd s0.fs.files x) w x.out
      ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) (.error ()) s0
      (by sep_focus) rfl ?_ ?_
    · exact ⟨hans_err.symm, by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], SeqEnv.inl hget_evs⟩
    wp_done
  | ok bs =>
    have hget_ok : .ok bs = x.own.get rd s0.fs.files (utf8 "registration-id") ∧
        sf.trace = s0.trace :=
      ⟨by simpa only [wp_norm, arm64_norm] using
            ‹(.ok bs : Except Unit (List (BitVec 8))) = _›,
       by simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›⟩
    rw [getResultAt_ok_sp_112 A.repAlloc s0.sp bs]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWP.exists_elim fun bCap => SepWP.exists_elim fun bPtr =>
      SepWP.pure_elim fun ⟨hbCap_le, hbCap_lt, hbPtr_ne⟩ => ?_
    by_cases hlen4 : bs.length = 4
    · match bs, hlen4 with
      | [b0, b1, b2, b3], _ =>
        have hans_ok : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files =
            .ok (b3 ++ b2 ++ b1 ++ b0) := by
          unfold IdGhost.regId
          rw [← hget_ok.1]
          rfl
        have hbCap_ne : bCap ≠ 0#64 := cap_ne_zero_of_cons hbCap_le
        have hbCap_beq : (bCap == 0#64) = false := beq_false_of_ne hbCap_ne
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl_sf
        apply sepWP_seg_ls_vm (Q := (blkPC_568).rebase (blkPl_568).base (hooksException H))
          blkLib_eq_568 (mid := lsρ lsRustDeallocSymCli)
        intro _m_strip
        apply SepWP.focus_rw (pointsToBytes4_eq_pointsTo32 bPtr b0 b1 b2 b3)
        wp_steps
        apply SepWP.focus_rw (pointsToBytes4_eq_pointsTo32 bPtr b0 b1 b2 b3).symm
        apply SepWP.focus_weaken (sp_112_ok_fold_48 s0.sp _ _ _ _ _)
        refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
          fun _m_real _hnsp => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        intro hcrl_d0
        wp_call_lscro hDeallocCells hcrl_d0
          ((bPtr, bCap, [b0, b1, b2, b3], s0.sp - 112#64), M.stepEvents w st)
        have hfs_sf1 : FsPost sf_1.fs := by
          simpa only [wp_norm, arm64_norm] using ‹FsPost sf_1.fs›
        have h_reg_b2 : sf_1.sp = s0.sp - 112#64 ∧
            sf_1.readReg64 (.gpr 19#5) = x.fut ∧
            sf_1.readReg64 (.gpr 20#5) = x.out ∧
            sf_1.readReg64 (.gpr 22#5) = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 :=
          ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        rcases h_reg_b2 with ⟨_, _, _, _⟩
        apply sepWP_seg_ls_vm (Q := (blkPC_568).rebase (blkPl_568).base (hooksException H))
          blkLib_eq_568 (mid := s0.readReg64 Reg.lr)
        intro _m_strip
        apply SepWP.focus_rw (out_48_reg_split x.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken (out_reg_ok_fold A.repAlloc x.out (b3 ++ b2 ++ b1 ++ b0) _ _ _ _ _)
        refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
          fun _m_real _hnsp => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        have henv_ok4 :
            CliIdRegIdPollEnv GetEnv rd s0.fs.files x
              (w ++ rustDeallocEvents bCap.toNat 1) :=
          SeqEnv.append hget_evs
            (Or.inr ⟨[], rustDeallocEvents bCap.toNat 1, rfl,
              by simp [OptRegIdMalformedEnv, ← hget_ok.1],
              FreeOnlyEvs.singleton 1 bCap.toNat⟩)
        refine focus_regPostPoolFs FsPost A lim st
          (M.stepEvents (rustDeallocEvents bCap.toNat 1) (M.stepEvents w st))
          (CliIdRegIdPollEnv GetEnv rd s0.fs.files x)
          (w ++ rustDeallocEvents bCap.toNat 1) x.out
          ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
          (.ok (b3 ++ b2 ++ b1 ++ b0)) s0
          (by sep_focus)
          (M.stepEvents_append w (rustDeallocEvents bCap.toNat 1) st).symm ?_ ?_
        · exact ⟨hans_ok.symm, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], henv_ok4⟩
        wp_done
    · have hans_err4 : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files = .error () := by
        unfold IdGhost.regId
        rw [← hget_ok.1]
        exact match_regId_ne_4 hlen4
      have hfit_alloc : FitsEvents M lim (M.stepEvents w st) (rustAllocEvents 14 1) :=
        CliIdRegIdPollEnv.fits_alloc14 hfit0 hget_evs hget_ok.1.symm hlen4
      have hlen_lt : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hbCap_le hbCap_lt
      have hne4_bv : BitVec.ofNat 64 bs.length ≠ 4#64 := len_bv_ne_four_of_ne hlen_lt hlen4
      have hne4_beq : (BitVec.ofNat 64 bs.length == 4#64) = false := beq_false_of_ne hne4_bv
      have hne4_sub : (BitVec.ofNat 64 bs.length - 4#64 == 0#64) = false :=
        beq_false_of_ne (fun h => hne4_bv (by bv_omega))
      have hne4_awc : (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~4#64) true).2.z = false := by
        unfold AddWithCarry64
        simp only [ite_true]
        exact beq_false_of_ne (fun h => hne4_bv (by bv_omega))
      apply sepWP_seq_lscro (mid := lsρ lsRustNoAllocShimSymCli) hcrl_sf
      apply sepWP_seg_ls_vm (Q := (blkPC_568).rebase (blkPl_568).base (hooksException H))
        blkLib_eq_568 (mid := lsρ lsRustNoAllocShimSymCli)
      intro _m_strip
      wp_steps
      apply SepWP.focus_weaken (sp_112_ok_fold_48 s0.sp _ _ _ _ _)
      refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by wp_norm_lhs))
        (hnext := ?_)
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hcrl_s
      wp_call_lscro hShimCells hcrl_s (s0.sp - 112#64)
      have hfs_sf1 : FsPost sf_1.fs := by
        simpa only [wp_norm, arm64_norm] using ‹FsPost sf_1.fs›
      refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      have h_reg_s : sf_1.sp = s0.sp - 112#64 ∧
          sf_1.readReg64 (.gpr 19#5) = x.fut ∧
          sf_1.readReg64 (.gpr 20#5) = x.out ∧
          sf_1.readReg64 (.gpr 21#5) = bPtr ∧
          sf_1.readReg64 (.gpr 23#5) = bCap :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩
      rcases h_reg_s with ⟨_, _, _, _, _⟩
      apply sepWP_seq_lscro (mid := lsρ lsRustAllocSymCli) hcrl_sf_1
      wp_steps_sync_pool (lsρ lsRustAllocSymCli)
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hcrl_a
      wp_call_lscro hAllocCells hcrl_a (s0.sp - 112#64, M.stepEvents w st)
      have hfs_sf2 : FsPost sf_2.fs := by
        simpa only [wp_norm, arm64_norm] using ‹FsPost sf_2.fs›
      have h_reg_a : sf_2.sp = s0.sp - 112#64 ∧
          sf_2.readReg64 (.gpr 19#5) = x.fut ∧
          sf_2.readReg64 (.gpr 20#5) = x.out ∧
          sf_2.readReg64 (.gpr 21#5) = bPtr ∧
          sf_2.readReg64 (.gpr 23#5) = bCap :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩
      rcases h_reg_a with ⟨_, _, _, _, _⟩
      have hbuf_ne : sf_2.readReg64 .x0 ≠ 0#64 := by assumption
      have hbuf_beq : (sf_2.readReg64 (.gpr 0#5) == 0#64) = false := beq_false_of_ne hbuf_ne
      by_cases hc0 : bCap = 0#64
      · subst hc0
        have hbs_nil : bs = [] := by
          cases bs with
          | nil => rfl
          | cons _ _ => simp at hbCap_le
        subst hbs_nil
        apply sepWP_seg_ls_vm (Q := (blkPC_568).rebase (blkPl_568).base (hooksException H))
          blkLib_eq_568 (mid := s0.readReg64 Reg.lr)
        intro _m_strip
        have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗
            vecU8BufRest A.repAlloc 0#64 bPtr 0) = emp := by
          simp [vecU8BufRest]
        apply SepWP.focus_rw hemp
        apply SepWP.focus_rw (memRegion_14_split_8_6 (sf_2.readReg64 .x0))
        wp_pull_exists
        apply SepWP.focus_rw (out_48_reg_split x.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken (write_14_overlap_mid (sf_2.readReg64 .x0) w0)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken (write_14_overlap_done (sf_2.readReg64 .x0) w0 wTail)
        apply SepWP.focus_weaken
          (out_reg_err_malformed_fold_budget A x.out (sf_2.readReg64 .x0) _ _
            ((unpack64 w0).take 6 ++ unpack64 wTail)
            hbuf_ne (write_14_overlap_length w0 wTail))
        refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
          fun _m_real _hnsp => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        have henv_mal0 :
            CliIdRegIdPollEnv GetEnv rd s0.fs.files x (w ++ rustAllocEvents 14 1) :=
          SeqEnv.append hget_evs
            (SeqEnv.inl (by simp [OptRegIdMalformedEnv, ← hget_ok.1]))
        refine focus_regPostPoolFs FsPost A lim st
          (M.stepEvents (rustAllocEvents 14 1) (M.stepEvents w st))
          (CliIdRegIdPollEnv GetEnv rd s0.fs.files x)
          (w ++ rustAllocEvents 14 1) x.out
          ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) (.error ()) s0
          (by sep_focus)
          (M.stepEvents_append w (rustAllocEvents 14 1) st).symm ?_ ?_
        · exact ⟨hans_err4.symm, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], henv_mal0⟩
        wp_done
      · have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
        apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl_sf_2
        apply sepWP_seg_ls_vm (Q := (blkPC_568).rebase (blkPl_568).base (hooksException H))
          blkLib_eq_568 (mid := lsρ lsRustDeallocSymCli)
        intro _m_strip
        apply SepWP.focus_rw (memRegion_14_split_8_6 (sf_2.readReg64 .x0))
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken (write_14_overlap_mid (sf_2.readReg64 .x0) w0)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken (write_14_overlap_done (sf_2.readReg64 .x0) w0 wTail)
        refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
          fun _m_real _hnsp => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        intro hcrl_d1
        wp_call_lscro hDeallocCells hcrl_d1
          ((bPtr, bCap, bs, s0.sp - 112#64),
            M.stepEvents (rustAllocEvents 14 1) (M.stepEvents w st))
        have hfs_sf3 : FsPost sf_3.fs := by
          simpa only [wp_norm, arm64_norm] using ‹FsPost sf_3.fs›
        have h_reg_d : sf_3.sp = s0.sp - 112#64 ∧
            sf_3.readReg64 (.gpr 19#5) = x.fut ∧
            sf_3.readReg64 (.gpr 20#5) = x.out ∧
            sf_3.readReg64 (.gpr 22#5) = sf_2.readReg64 .x0 :=
          ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        rcases h_reg_d with ⟨_, _, _, _⟩
        apply sepWP_seg_ls_vm (Q := (blkPC_568).rebase (blkPl_568).base (hooksException H))
          blkLib_eq_568 (mid := s0.readReg64 Reg.lr)
        intro _m_strip
        apply SepWP.focus_rw (out_48_reg_split x.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken
          (out_reg_err_malformed_fold_budget A x.out (sf_2.readReg64 .x0) _ _
            ((unpack64 w0).take 6 ++ unpack64 wTail)
            hbuf_ne (write_14_overlap_length w0 wTail))
        refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
          fun _m_real _hnsp => ?_
        refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by wp_norm_lhs))
          (hnext := ?_)
        have henv_mal1 :
            CliIdRegIdPollEnv GetEnv rd s0.fs.files x
              (w ++ (rustAllocEvents 14 1 ++ rustDeallocEvents bCap.toNat 1)) :=
          SeqEnv.append hget_evs
            (SeqEnv.append (by simp [OptRegIdMalformedEnv, ← hget_ok.1, hlen4])
              (FreeOnlyEvs.singleton 1 bCap.toNat))
        refine focus_regPostPoolFs FsPost A lim st
          (M.stepEvents (rustDeallocEvents bCap.toNat 1)
            (M.stepEvents (rustAllocEvents 14 1) (M.stepEvents w st)))
          (CliIdRegIdPollEnv GetEnv rd s0.fs.files x)
          (w ++ (rustAllocEvents 14 1 ++ rustDeallocEvents bCap.toNat 1)) x.out
          ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) (.error ()) s0
          (by sep_focus)
          (by rw [M.stepEvents_append, M.stepEvents_append]) ?_ ?_
        · exact ⟨hans_err4.symm, by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *], henv_mal1⟩
        wp_done

/-! ## Two-Sided `withFdsGe3Closed` Outer Contracts (`*_fd`) -/

theorem idRegIdPollSpecPlaced_mono_env_fd [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PollEnv₁ PollEnv₂ : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {stk : Nat}
    (hsub : ∀ F0 x evs, PollEnv₁ F0 x evs → PollEnv₂ F0 x evs)
    (hok : subroutine_ok prog entry
      (withFdsGe3Closed (idRegIdPollSpecPlaced rd pathOk A lim PollEnv₁ stk))) :
    subroutine_ok prog entry
      (withFdsGe3Closed (idRegIdPollSpecPlaced rd pathOk A lim PollEnv₂ stk)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hfds, hp⟩ := extract_withFdsGe3Closed hp
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds, ?_⟩
    unfold idRegIdPollSpecPlaced at hp ⊢
    obtain ⟨hcrl, hp⟩ := extract_withLsCodeRoLoaded hp
    refine satisfies_lscro_pre hcrl ?_
    dsimp only at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hx0, hx8, hpath, hpok, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx8, hpath, hpok, FitsEnv.mono (hsub s.fs.files x) hfit⟩, hmem⟩
  · obtain ⟨hfds, hq⟩ := extract_withFdsGe3Closed_post hq
    dsimp only [withFdsGe3Closed, idRegIdPollSpecPlaced, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hans, htr, henv⟩, hmem⟩
    exact ⟨⟨hans, htr, hsub s0.fs.files x evs henv⟩, hmem⟩

set_option maxRecDepth 2000000 in
theorem idRegIdPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok (lsProg_568 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hstk : 0x70 + regCalleeStk getStk ≤ stk) :
    subroutine_ok (lsProg_568 H) (lsmpl.base 568)
      (withFdsGe3Closed
        (idRegIdPollSpecPlaced rd pathOk A lim (CliIdRegIdPollEnv GetEnv rd) stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [idRegIdPollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hpath, hpok, hfit⟩, hmem⟩
  dsimp only [idOwnFutBoxAtPlaced] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64
      (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₈ 0#8) ∗ memRegion (x.fut + 9#64) 7 ∗
        dirAt A.repAlloc x.self x.own ∗ memRegion x.out 48 ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  let calleeStk := regCalleeStk getStk
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 112 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 112) (by omega) hstk_hi,
      ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi] at hmem
  obtain ⟨w0, wTail, hro⟩ := rodata_regId_and_malformed_placed hcrl0.2 hmem
  let F_extra :=
    memRegion (x.fut + 9#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliIdRegIdPollInnerPlacedSpecFs FdsGe3Closed rd pathOk A lim
          (CliIdRegIdPollEnv GetEnv rd) w0 wTail calleeStk)).pre (x, st) s0 ∗ (F_extra ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hcrl0 ?_
    dsimp only [cliIdRegIdPollInnerPlacedSpecFs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfds0, hx0, hx8, hpath, hpok, hfit⟩, ?_⟩
    dsimp only [F_extra]
    exact Satisfies.mono (by sep_focus) hro
  have hGetCells := dirGetRoFs_cells_placed_ok_fd (calleeStk := calleeStk) hGet
    (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi
  have hDeallocCells := deallocAt_cells_placed_ok_fd (prog := lsProg_568 H)
    (calleeStk := calleeStk) hC (by decide)
    (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi
  have hShimCells := subroutine_ok_lscro_withFdsGe3Closed_of_lscro_keepsFs
    (shimAt_cells_vm_keepsFs_placed_ok (prog := lsProg_568 H) (calleeStk := calleeStk) hC
      (by decide) (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi)
  have hAllocCells := subroutine_ok_lscro_withFdsGe3Closed_of_lscro_keepsFs
    (alloc14At_cells_keepsFs_placed_ok (prog := lsProg_568 H) (calleeStk := calleeStk)
      (AllocContractsFsPlaced.toAllocContractsX hC) (by decide)
      (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi)
  refine (idRegIdPollInner_fsPost_placed_ok (w0 := w0) (wTail := wTail) (fun _ h => h)
    hGetCells hDeallocCells hShimCells hAllocCells).mono_outcome
    (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpecFs, withFdsGe3Closed,
      idRegIdPollSpecPlaced, idOwnFutBoxAtPlaced, regPostPoolFs] at hq ⊢
    simp_rw [idRegIdOutAtPlaced_eq]
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, ans, hq⟩
    have hq_pure : sf.mem ⊨
        ⌜ans = (IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧
          sf.trace = s0.trace ∧ FdsGe3Closed sf.fs ∧
          CliIdRegIdPollEnv GetEnv rd s0.fs.files x evs⌝ ∗
        (((lsρ idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
            (lsρ malformedFileStrSym ↦₆₄ᵣ w0) ∗
            ((lsρ malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail)) ∗
          (idRegIdOutAt A.repAlloc x.out ans ∗
            ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗ memRegion (x.fut + 9#64) 7) ∗
            dirAt A.repAlloc x.self x.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112)) ∗
              (stackAt (s0.sp - 112#64) calleeStk ∗ cells (s0.sp - 112#64) 14))) ∗ R) := by
      dsimp only [F_extra] at hq
      exact Satisfies.mono (by sep_focus) hq
    rw [satisfies_pure_sepConj] at hq_pure
    rcases hq_pure with ⟨⟨hans, htr, hfdsf, henv⟩, hq_ro⟩
    have hq_drop := Satisfies.of_sep_right hq_ro
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ans, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 112) (by omega) hstk_hi,
        ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hans, htr, henv⟩, ?_⟩
    rw [show BitVec.ofNat 64 (8 * 14) = 112#64 from rfl]
    convert hq_drop using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [cliIdRegIdPollInnerPlacedSpecFs, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem idRegIdPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg : Program} {callerBlk getBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hstk : 0x70 + regCalleeStk getStk ≤ stk)
    (hblk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 568)
      (withFdsGe3Closed
        (idRegIdPollSpecPlaced rd pathOk A lim (CliIdRegIdPollEnv GetEnv rd) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 568)
    (idRegIdPoll_placed_ok_of_deps_fd hC
      (ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_568 H) (j := getBlk)
        hGet (by decide) hGetBlk hGetUnmut)
      hstk)
    hblk

/-- CLI instantiation of `IdentityFiles::get_local_registration_id::{closure#0}` (Block `568`)
with two-sided `withFdsGe3Closed` at residual stack `stk - cliInitiateFrame`. -/
theorem idRegIdPoll_cli_placed_ok_fd [LibsignalPlacement] {prog getProg : Program}
    {i getBlk : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [IsLsBlockProg prog i H] [IsLsBlockProg getProg getBlk H]
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    (B : RunBudgets)
    (hC : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced cliIo.rd cliWrOk A lim GetEnv B.dirGetNeed)))
    (hi : i < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok prog (lsmpl.base 568)
      (withFdsGe3Closed
        (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim (CliIdRegIdPollEnv GetEnv cliIo.rd)
          (stk - cliInitiateFrame))) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have he : extHookStack ≤ 65536 := by decide
  exact idRegIdPoll_placed_caller_ok_of_deps_fd hC hGet
    (by dsimp only [regCalleeStk]; omega) hi hGetBlk hGetUnmut

/-! ## Pre-Only `FdsGe3Closed` Outer Contracts (`*_preFd`) -/

set_option maxRecDepth 2000000 in
theorem idRegIdPoll_preFd_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok (lsProg_568 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hstk : 0x70 + regCalleeStk getStk ≤ stk) :
    subroutine_ok (lsProg_568 H) (lsmpl.base 568)
      (withPreGuard (fun s => FdsGe3Closed s.fs)
        (idRegIdPollSpecPlaced rd pathOk A lim (CliIdRegIdPollEnv GetEnv rd) stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withPreGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfds0, hpre⟩ := hpre
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [idRegIdPollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hpath, hpok, hfit⟩, hmem⟩
  dsimp only [idOwnFutBoxAtPlaced] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64
      (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₈ 0#8) ∗ memRegion (x.fut + 9#64) 7 ∗
        dirAt A.repAlloc x.self x.own ∗ memRegion x.out 48 ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  let calleeStk := regCalleeStk getStk
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 112 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 112) (by omega) hstk_hi,
      ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi] at hmem
  obtain ⟨w0, wTail, hro⟩ := rodata_regId_and_malformed_placed hcrl0.2 hmem
  let F_extra :=
    memRegion (x.fut + 9#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliIdRegIdPollInnerPlacedSpecFs (fun _ => True) rd pathOk A lim
          (CliIdRegIdPollEnv GetEnv rd) w0 wTail calleeStk)).pre (x, st) s0 ∗ (F_extra ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hcrl0 ?_
    dsimp only [cliIdRegIdPollInnerPlacedSpecFs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfds0, hx0, hx8, hpath, hpok, hfit⟩, ?_⟩
    dsimp only [F_extra]
    exact Satisfies.mono (by sep_focus) hro
  have hGetCells := dirGetRoFs_cells_placed_ok_fd (calleeStk := calleeStk) hGet
    (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi
  have hDeallocCells := subroutine_ok_lscro_withFsPred_true
    (deallocAt_cells_placed_ok (prog := lsProg_568 H) (calleeStk := calleeStk) hC (by decide)
      (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi)
  have hShimCells := subroutine_ok_lscro_withFsPred_true
    (shimAt_cells_vm_placed_ok (prog := lsProg_568 H) (calleeStk := calleeStk) hC (by decide)
      (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi)
  have hAllocCells := subroutine_ok_lscro_withFsPred_true
    (alloc14At_cells_placed_ok (prog := lsProg_568 H) (calleeStk := calleeStk) hC (by decide)
      (by dsimp [calleeStk, regCalleeStk]; omega) hcal_hi)
  refine (idRegIdPollInner_fsPost_placed_ok (w0 := w0) (wTail := wTail) (fun _ _ => trivial)
    hGetCells hDeallocCells hShimCells hAllocCells).mono_outcome
    (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpecFs, withPreGuard,
      idRegIdPollSpecPlaced, idOwnFutBoxAtPlaced, regPostPoolFs] at hq ⊢
    simp_rw [idRegIdOutAtPlaced_eq]
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    have hq_pure : sf.mem ⊨
        ⌜ans = (IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧
          sf.trace = s0.trace ∧ True ∧
          CliIdRegIdPollEnv GetEnv rd s0.fs.files x evs⌝ ∗
        (((lsρ idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
            (lsρ malformedFileStrSym ↦₆₄ᵣ w0) ∗
            ((lsρ malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail)) ∗
          (idRegIdOutAt A.repAlloc x.out ans ∗
            ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗ memRegion (x.fut + 9#64) 7) ∗
            dirAt A.repAlloc x.self x.own ∗ A.pool lim (M.stepEvents evs st) sf ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112)) ∗
              (stackAt (s0.sp - 112#64) calleeStk ∗ cells (s0.sp - 112#64) 14))) ∗ R) := by
      dsimp only [F_extra] at hq
      exact Satisfies.mono (by sep_focus) hq
    rw [satisfies_pure_sepConj] at hq_pure
    rcases hq_pure with ⟨⟨hans, htr, _, henv⟩, hq_ro⟩
    have hq_drop := Satisfies.of_sep_right hq_ro
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 112) (by omega) hstk_hi,
        ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hans, htr, henv⟩, ?_⟩
    rw [show BitVec.ofNat 64 (8 * 14) = 112#64 from rfl]
    convert hq_drop using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [cliIdRegIdPollInnerPlacedSpecFs, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem ls_transfer_preFd_lscro [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (withPreGuard (fun s => FdsGe3Closed s.fs) (withLsCodeRoLoaded lsmpl spec)))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry
      (withPreGuard (fun s => FdsGe3Closed s.fs) (withLsCodeRoLoaded lsmpl spec)) := by
  have hin : subroutine_ok calleeProg entry
      (withLsCodeRoLoaded lsmpl (withPreGuard (fun s => FdsGe3Closed s.fs) spec)) :=
    subroutine_ok_mono hcallee
      (fun _ _ _ hp => by
        obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hp
        dsimp only [withPreGuard] at hpre ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
        exact ⟨hpre.1, satisfies_lscro_pre hcrl hpre.2⟩)
      (fun _ _ _ _ hq => hq)
  have hout := ls_transfer_lscro (callerProg := callerProg) (j := j) hin hi hj hj_unmut
  exact subroutine_ok_mono hout
    (fun _ _ _ hp => by
      dsimp only [withPreGuard] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      obtain ⟨hfds, hp⟩ := hp
      obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hp
      refine satisfies_lscro_pre hcrl ?_
      dsimp only [withPreGuard]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hfds, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem idRegIdPoll_preFd_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg : Program} {callerBlk getBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hstk : 0x70 + regCalleeStk getStk ≤ stk)
    (hblk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 568)
      (withPreGuard (fun s => FdsGe3Closed s.fs)
        (idRegIdPollSpecPlaced rd pathOk A lim (CliIdRegIdPollEnv GetEnv rd) stk)) :=
  ls_transfer_preFd_lscro (callerProg := callerProg) (j := 568)
    (idRegIdPoll_preFd_placed_ok_of_deps hC
      (ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_568 H) (j := getBlk)
        hGet (by decide) hGetBlk hGetUnmut)
      hstk)
    hblk

/-- Pre-only `FdsGe3Closed` CLI instantiation of `IdentityFiles::get_local_registration_id::{closure#0}`
(Block `568`) directly from `RunHooksPlaced` (`hh.alloc`) and `withFdsGe3Closed (dirGetSpecPlaced …)`. -/
theorem idRegIdPoll_cli_preFd_placed_ok [LibsignalPlacement] {prog getProg : Program}
    {i getBlk : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {W : CliHooks} {H : LibsignalHooks}
    [IsLsBlockProg prog i H] [IsLsBlockProg getProg getBlk H]
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    (B : RunBudgets)
    (hh : RunHooksPlaced W A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced cliIo.rd cliWrOk A lim GetEnv B.dirGetNeed)))
    (hi : i < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok prog (lsmpl.base 568)
      (withPreGuard (fun s => FdsGe3Closed s.fs)
        (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim (CliIdRegIdPollEnv GetEnv cliIo.rd)
          (stk - cliInitiateFrame))) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have he : extHookStack ≤ 65536 := by decide
  exact idRegIdPoll_preFd_placed_caller_ok_of_deps hh.alloc hGet
    (by dsimp only [regCalleeStk]; omega) hi hGetBlk hGetUnmut

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudgetFd
