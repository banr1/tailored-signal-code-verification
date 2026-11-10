/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded `IdentityFiles::get_identity_key_pair::{closure#0}` (`[LibsignalPlacement]`, Block `567`)

Provides two-sided `withFdsGe3Closed` (`*_fd`) and pre-only `FdsGe3Closed` (`*_preFd`) contracts
for `IdentityFiles::get_identity_key_pair::{closure#0}` (Block `567`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdGhost ReadRule dirAt pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (blkLib_eq_567 blkPC_567 blkPl_567 lsProg_567)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (IdOwnPollGhostPlaced idOwnFutBoxAtPlaced satisfies_withLsCodeRoLoaded_pre
   stk_sub_ge_base stk_sub_ge_dirGet)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll (kpCalleeStk)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll.KpNorm
  (awc_okTagVec_two awc_speWord1_two extractLsb_append_hi extractLsb_append_lo
   fs_setMem_pre fs_setPC_pre fs_setPState_pre fs_writeReg32_pre fs_writeReg64_pre
   fs_writeReg_pre fs_writeVReg128_pre mem_writeVReg128_pre okTagVec_eq_neg2
   pc_writeVReg128_pre pstate_writeVReg128_pre readReg32_setMem_setPC_pre
   readReg32_setPC_pre readReg32_writeVReg128_pre readReg64_setMem_setPC_pre
   readReg64_setPC_pre readReg64_writeVReg128_pre readReg_setMem_setPC_pre
   readReg_setPC_pre readReg_writeVReg128_pre readVReg128_setMem_pre
   readVReg128_setMem_setPC_pre readVReg128_setPC_pre readVReg128_setPState_pre
   readVReg128_writeReg32_pre readVReg128_writeReg64_pre readVReg128_writeReg_pre
   readVReg128_writeVReg128_pre sp_setMem_setPC_pre sp_setPC_pre sp_writeVReg128_pre
   speWord_one_eq status_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
   trace_writeVReg128_pre)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon
  (idKeyPairOutAtPlaced_eq idKpFileNameSym reloc_idKeyPairOutAt
   rodata_idKpFileName_placed utf8_idKp_length)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs (idKeyPairOutAt)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
  (memRegion_bound_of_pointsTo64 stackAt_sub_split vecU8BufRest)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (IdentityKeyPairTryFromEnv RecordCodecLoopEnv identityKeyPairTryFromPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro withPreGuard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (CliIdKeyPairPollEnv OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudget
  (deallocAt_cells_placed_ok ikpTryFromCellsPlacedSpec ikpTryFrom_cells_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd
  (cells_22_kp_placed deallocAt_cells_placed_ok_fd dirGetRoFsCellsSpec_fd
   dirGetRoFs_cells_placed_ok_fd extract_withFdsGe3Closed_post getResultAt_err_sp_96_placed
   getResultAt_ok_sp_96_placed ikpTryFrom_cells_placed_ok_fd kp72_words_fold_memRegion_placed
   kp72_words_sp168_placed memRegion_72_eq_cells9_placed sp_168_err_fold_placed
   sp_168_err_split_placed sp_96_cells4_fold_48_placed sp_96_cells6_fold_48_placed
   tryFrom_to_idKeyPairOutAt_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced AllocContractsXCliPlaced dirGetSpecPlaced idKeyPairPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.CalleesBudget (deallocVecBufSpec)

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
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre fs_writeVReg128_pre
  trace_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre readVReg128_writeVReg128_pre
  pc_writeVReg128_pre pstate_writeVReg128_pre mem_writeVReg128_pre status_writeVReg128_pre
  speWord_one_eq okTagVec_eq_neg2 awc_speWord1_two awc_okTagVec_two
  extractLsb_append_lo extractLsb_append_hi

attribute [local arm64_norm]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre fs_writeVReg128_pre
  trace_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre readVReg128_writeVReg128_pre
  pc_writeVReg128_pre pstate_writeVReg128_pre mem_writeVReg128_pre status_writeVReg128_pre
  speWord_one_eq okTagVec_eq_neg2 awc_speWord1_two awc_okTagVec_two
  extractLsb_append_lo extractLsb_append_hi

attribute [local irreducible] Program.fetch Program.externAt? FitsEnv

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

private def kpPostPoolPlacedFs {M : AllocCostModel} (FsPost : FsState → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (Env : List AllocEvent → Prop) (out : BitVec 64)
    (expected : Except Unit IdentityKeyPair) (s0 sf : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ∃∗ ans : Except Unit IdentityKeyPair,
    ⌜ans = expected ∧ sf.trace = s0.trace ∧ FsPost sf.fs ∧ Env evs⌝ ∗
      idKeyPairOutAt A.repAlloc out ans ∗ A.pool lim (M.stepEvents evs st) sf

private theorem kpPostPoolPlacedFs_intro {M : AllocCostModel} (FsPost : FsState → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st st_cur : M.σ)
    (Env : List AllocEvent → Prop) (evs : List AllocEvent) (out : BitVec 64)
    (expected ans : Except Unit IdentityKeyPair) (B : List (BitVec 8) → SepProp)
    (bs : List (BitVec 8)) (s0 sf : State)
    (hB : idKeyPairOutAt A.repAlloc out ans =
      ∃∗ bs' : List (BitVec 8), ⌜bs'.length = 72⌝ ∗ (out ↦ₛ bs') ∗ B bs')
    (hbs : bs.length = 72)
    (hst : st_cur = M.stepEvents evs st)
    (hpure : ans = expected ∧ sf.trace = s0.trace ∧ FsPost sf.fs ∧ Env evs) :
    ((out ↦ₛ bs) ∗ B bs) ∗ A.pool lim st_cur sf ⊢
      kpPostPoolPlacedFs FsPost A lim st Env out expected s0 sf := by
  subst hst
  have htrue : ((ans = expected ∧ sf.trace = s0.trace ∧ FsPost sf.fs ∧ Env evs) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  have hlen_true : ((bs.length = 72) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hbs⟩
  unfold kpPostPoolPlacedFs
  refine Entails.sepExists_right evs (Entails.sepExists_right ans ?_)
  rw [htrue, pure_true, emp_sepConj]
  refine sepConj_mono_left ?_
  rw [hB]
  refine Entails.sepExists_right bs ?_
  rw [hlen_true, pure_true, emp_sepConj]
  exact Entails.refl _

private theorem focus_kpPostPoolPlacedFs {M : AllocCostModel} (FsPost : FsState → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st st_cur : M.σ)
    (Env : List AllocEvent → Prop) (evs : List AllocEvent) (out : BitVec 64)
    (expected ans : Except Unit IdentityKeyPair) (B : List (BitVec 8) → SepProp)
    (bs : List (BitVec 8)) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hB : idKeyPairOutAt A.repAlloc out ans =
      ∃∗ bs' : List (BitVec 8), ⌜bs'.length = 72⌝ ∗ (out ↦ₛ bs') ∗ B bs')
    (hbs : bs.length = 72)
    (hf : P = (((out ↦ₛ bs) ∗ B bs) ∗ A.pool lim st_cur s_ret) ∗ R)
    (hst : st_cur = M.stepEvents evs st)
    (hpure : ans = expected ∧ s_ret.trace = s0.trace ∧ FsPost s_ret.fs ∧ Env evs)
    (hnext : SepWP prog ret_pc s_ret
      (kpPostPoolPlacedFs FsPost A lim st Env out expected s0 s_ret ∗ R) post oom) :
    SepWP prog ret_pc s_ret P post oom :=
  SepWP.focus_weaken
    (kpPostPoolPlacedFs_intro FsPost A lim st st_cur Env evs out expected ans B bs s0 s_ret
      hB hbs hst hpure)
    (hf := hf) hnext

private def cliIdKeyPairPollInnerPlacedSpecFs [LibsignalPlacement] {M : AllocCostModel}
    (FsPost : FsState → Prop) (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (calleeStk : Nat) :
    Spec (IdOwnPollGhostPlaced × M.σ) where
  pre := fun (x, st) s =>
    ⌜FdsGe3Closed s.fs ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "identity-key-pair")) ∧
      (∀ bs, x.own.get rd s.fs.files (utf8 "identity-key-pair") = .ok bs →
        bs.length < 2 ^ 32) ∧
      FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
      (lsρ idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      memRegion x.out 72 ∗ lsLogOff ∗ A.pool lim st s ∗
      stackAt (s.sp - 176#64) calleeStk ∗ cells (s.sp - 176#64) 22
  post := fun (x, st) s0 sf =>
    kpPostPoolPlacedFs FsPost A lim st (PollEnv s0.fs.files x) x.out
        ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files) s0 sf ∗
      (lsρ idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      lsLogOff ∗
      stackAt (s0.sp - 176#64) calleeStk ∗ cells (s0.sp - 176#64) 22

private def cliIdKeyPairPollExpandedPlacedSpecFs [LibsignalPlacement] {M : AllocCostModel}
    (FsPost : FsState → Prop) (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (calleeStk : Nat) :
    Spec (IdOwnPollGhostPlaced × M.σ) where
  pre := fun (x, st) s =>
    ⌜FdsGe3Closed s.fs ∧ s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "identity-key-pair")) ∧
      (∀ bs, x.own.get rd s.fs.files (utf8 "identity-key-pair") = .ok bs →
        bs.length < 2 ^ 32) ∧
      FitsEnv M lim st (PollEnv s.fs.files x)⌝ ∗
      (lsρ idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      memRegion x.out 72 ∗ lsLogOff ∗ A.pool lim st s ∗
      stackAt (s.sp - 176#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s.sp - 176#64) ↦₆₄ v0) ∗
        memRegion (s.sp - 168#64) 72 ∗
        memRegion (s.sp - 96#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s.sp - 48#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s.sp - 40#64) ↦₆₄ s30) ∗
        (∃∗ s22 : BitVec 64, (s.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s.sp - 8#64) ↦₆₄ s19))
  post := fun (x, st) s0 sf =>
    kpPostPoolPlacedFs FsPost A lim st (PollEnv s0.fs.files x) x.out
        ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files) s0 sf ∗
      (lsρ idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A.repAlloc x.self x.own ∗
      lsLogOff ∗
      stackAt (s0.sp - 176#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v0) ∗
        memRegion (s0.sp - 168#64) 72 ∗
        memRegion (s0.sp - 96#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s0.sp - 48#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s0.sp - 40#64) ↦₆₄ s30) ∗
        (∃∗ s22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s19))

private theorem cliIdKeyPairPollExpandedPlacedSpecFs_eq [LibsignalPlacement] {M : AllocCostModel}
    (FsPost : FsState → Prop) (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop)
    (calleeStk : Nat) :
    cliIdKeyPairPollExpandedPlacedSpecFs FsPost rd pathOk A lim PollEnv calleeStk =
      cliIdKeyPairPollInnerPlacedSpecFs FsPost rd pathOk A lim PollEnv calleeStk := by
  unfold cliIdKeyPairPollExpandedPlacedSpecFs cliIdKeyPairPollInnerPlacedSpecFs
  congr 1
  · funext ⟨x, st⟩ s; rw [cells_22_kp_placed s.sp]
  · funext ⟨x, st⟩ s0 sf; rw [cells_22_kp_placed s0.sp]

set_option pp.deepTerms false in
set_option pp.maxSteps 1000000 in
set_option maxHeartbeats 1600000 in
private theorem idKeyPairPollInner_fsPost_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {FsPost : FsState → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    (himp : ∀ fs, FdsGe3Closed fs → FsPost fs)
    (hGetCells : subroutine_ok (lsProg_567 H) (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetRoFsCellsSpec_fd rd pathOk A lim GetEnv (kpCalleeStk getStk))))
    (hTryCells : subroutine_ok (lsProg_567 H) (lsmpl.base 84)
      (withLsCodeRoLoaded lsmpl
        (withFsPred FsPost (ikpTryFromCellsPlacedSpec A lim (kpCalleeStk getStk)))))
    (hDeallocCells : subroutine_ok (lsProg_567 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl
        (withFsPred FsPost (deallocVecBufSpec A lim (kpCalleeStk getStk))))) :
    subroutine_ok (lsProg_567 H) (blkPl_567).base
      (withLsCodeRoLoaded lsmpl
        (cliIdKeyPairPollInnerPlacedSpecFs FsPost rd pathOk A lim
          (CliIdKeyPairPollEnv GetEnv rd) (kpCalleeStk getStk))) := by
  rw [← cliIdKeyPairPollExpandedPlacedSpecFs_eq]
  dsimp only [dirGetRoFsCellsSpec_fd, withFdsGe3Closed, withFsPred]
    at hGetCells hTryCells hDeallocCells
  dsimp only [lsProg_567, ite_true] at hGetCells hTryCells hDeallocCells ⊢
  change subroutine_ok ((blkPC_567).rebase (blkPl_567).base H) (blkPl_567).base _
  dsimp only [withLsCodeRoLoaded]
  simp (config := { maxSteps := 2000000 }) only [cliIdKeyPairPollExpandedPlacedSpecFs,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init xs s0
  obtain ⟨x, st⟩ := xs
  dsimp only at *
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfds0 : FdsGe3Closed s0.fs := by assumption
  have hfit0 : FitsEnv M lim st (CliIdKeyPairPollEnv GetEnv rd s0.fs.files x) := by assumption
  have hfit_get : FitsEnv M lim st (GetEnv s0.fs.files x.own (utf8 "identity-key-pair")) :=
    CliIdKeyPairPollEnv.fits_get hfit0
  have hname_len : (utf8 "identity-key-pair").length = 17 := utf8_idKp_length
  have hname_lt : (utf8 "identity-key-pair").length < 2 ^ 32 := by
    rw [utf8_idKp_length]; decide
  apply sepWP_seq_lscro (mid := lsmpl.base 589) hcrl0
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro hGetCells hcrl1
    ((s0.sp - 96#64, x.self, x.own,
      lsρ idKpFileNameSym, utf8 "identity-key-pair", s0.sp - 176#64), st)
  have hfds_sf : FdsGe3Closed sf.fs := by
    simpa only [wp_norm, arm64_norm] using ‹FdsGe3Closed sf.fs›
  have hfs_sf : FsPost sf.fs := himp sf.fs hfds_sf
  have hget_evs : GetEnv s0.fs.files x.own (utf8 "identity-key-pair") w := by
    simpa only [wp_norm, arm64_norm] using ‹GetEnv _ x.own (utf8 "identity-key-pair") w›
  have h_reg0 : sf.sp = s0.sp - 176#64 ∧
      sf.readReg64 (.gpr 19#5) = x.fut ∧
      sf.readReg64 (.gpr 20#5) = x.out ∧
      sf.readReg64 (.gpr 29#5) = s0.sp - 48#64 :=
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  rcases h_reg0 with ⟨_, _, _, _⟩
  cases w_1 with
  | error u =>
    cases u
    have hget_err : .error () = x.own.get rd s0.fs.files (utf8 "identity-key-pair") ∧
        sf.trace = s0.trace :=
      ⟨by simpa only [wp_norm, arm64_norm] using
            ‹(.error () : Except Unit (List (BitVec 8))) = _›,
       by simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›⟩
    have hans_err : (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files = .error () := by
      unfold IdGhost.keyPair
      rw [← hget_err.1]
      rfl
    apply sepWP_seg_ls_vm (Q := (blkPC_567).rebase (blkPl_567).base (hooksException H))
      blkLib_eq_567 (mid := s0.readReg64 Reg.lr)
    intro _m_strip
    apply SepWP.focus_rw (getResultAt_err_sp_96_placed A.repAlloc s0.sp)
    wp_pull_exists
    apply SepWP.focus_rw (sp_168_err_split_placed s0.sp)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_weaken (sp_96_cells6_fold_48_placed s0.sp _ _ _ _ _ _)
    apply SepWP.focus_weaken (sp_168_err_fold_placed A.repAlloc s0.sp _ _ _ _)
    rcases reloc_idKeyPairOutAt A.repAlloc (.error ()) with ⟨B, hB⟩
    apply SepWP.focus_rw (hB (s0.sp - 168#64))
    wp_pull_exists
    apply SepWP.pure_elim; intro hbs72
    rcases kp72_words_sp168_placed s0.sp x.out hbs72 with
      ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hsp72, hout72⟩
    apply SepWP.focus_rw hsp72
    apply SepWP.focus_rw (memRegion_72_eq_cells9_placed x.out)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_rw hout72.symm
    apply SepWP.focus_weaken (kp72_words_fold_memRegion_placed s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8)
    refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    refine focus_kpPostPoolPlacedFs FsPost A lim st (M.stepEvents w st)
      (CliIdKeyPairPollEnv GetEnv rd s0.fs.files x) w x.out
      ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files) (.error ()) B _ s0
      (hB x.out) hbs72 (by sep_focus) rfl ?_ ?_
    · exact ⟨hans_err.symm, by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], SeqEnv.inl hget_evs⟩
    wp_done
  | ok bs =>
    have hget_ok : .ok bs = x.own.get rd s0.fs.files (utf8 "identity-key-pair") ∧
        sf.trace = s0.trace :=
      ⟨by simpa only [wp_norm, arm64_norm] using
            ‹(.ok bs : Except Unit (List (BitVec 8))) = _›,
       by simpa only [wp_norm, arm64_norm] using ‹sf.trace = _›⟩
    have hbs_lt32 : bs.length < 2 ^ 32 := by
      have hall : ∀ bs, x.own.get rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
          bs.length < 2 ^ 32 := by assumption
      exact hall bs hget_ok.1.symm
    have hfit_try : FitsEnv M lim (M.stepEvents w st)
        (RecordCodecLoopEnv (2 * bs.length + 3) bs.length) :=
      CliIdKeyPairPollEnv.fits_tryFrom hfit0 hget_evs hget_ok.1.symm
    have hx1_len : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    let ansOk : Except Unit IdentityKeyPair :=
      match IdentityKeyPair.tryFrom bs with
      | .ok kp => .ok kp
      | .error _ => .error ()
    have hans_ok : (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files = ansOk := by
      unfold IdGhost.keyPair
      rw [← hget_ok.1]
      rfl
    rw [getResultAt_ok_sp_96_placed A.repAlloc s0.sp bs]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWP.exists_elim fun bCap => SepWP.exists_elim fun bPtr =>
      SepWP.pure_elim fun ⟨hbCap_le, hbCap_lt, hbPtr_ne⟩ => ?_
    apply sepWP_seq_lscro (mid := lsmpl.base 84) hcrl_sf
    apply sepWP_seg_ls_vm (Q := (blkPC_567).rebase (blkPl_567).base (hooksException H))
      blkLib_eq_567 (mid := lsmpl.base 84)
    intro _m_strip
    wp_steps
    apply SepWP.focus_weaken (sp_96_cells4_fold_48_placed s0.sp _ _ _ _)
    refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
    intro hcrl_try
    wp_call_lscro hTryCells hcrl_try
      ((bPtr, bs, s0.sp - 168#64, s0.sp - 176#64), M.stepEvents w st)
    have hfs_sf1 : FsPost sf_1.fs := by
      simpa only [wp_norm, arm64_norm] using ‹FsPost sf_1.fs›
    have htry_evs : IdentityKeyPairTryFromEnv bs.length w_1 := by
      simpa only [wp_norm, arm64_norm] using ‹IdentityKeyPairTryFromEnv bs.length w_1›
    have h_reg1 : sf_1.sp = s0.sp - 176#64 ∧
        sf_1.readReg64 (.gpr 19#5) = x.fut ∧
        sf_1.readReg64 (.gpr 20#5) = x.out ∧
        sf_1.readReg64 (.gpr 21#5) = bCap ∧
        sf_1.readReg64 (.gpr 22#5) = bPtr ∧
        sf_1.readReg64 (.gpr 29#5) = s0.sp - 48#64 :=
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    rcases h_reg1 with ⟨_, _, _, _, _, _⟩
    by_cases hc0 : bCap = 0#64
    · subst hc0
      have hbs_nil : bs = [] := by
        cases bs with
        | nil => rfl
        | cons _ _ => simp at hbCap_le
      subst hbs_nil
      apply sepWP_seg_ls_vm (Q := (blkPC_567).rebase (blkPl_567).base (hooksException H))
        blkLib_eq_567 (mid := s0.readReg64 Reg.lr)
      intro _m_strip
      have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗
          vecU8BufRest A.repAlloc 0#64 bPtr 0) = emp := by
        simp [vecU8BufRest]
      apply SepWP.focus_rw hemp
      apply SepWP.focus_weaken (tryFrom_to_idKeyPairOutAt_placed A.repAlloc (s0.sp - 168#64)
        (IdentityKeyPair.tryFrom []))
      rcases reloc_idKeyPairOutAt A.repAlloc ansOk with ⟨B, hB⟩
      apply SepWP.focus_rw (hB (s0.sp - 168#64))
      wp_pull_exists
      apply SepWP.pure_elim; intro hbs72
      rcases kp72_words_sp168_placed s0.sp x.out hbs72 with
        ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hsp72, hout72⟩
      apply SepWP.focus_rw hsp72
      apply SepWP.focus_rw (memRegion_72_eq_cells9_placed x.out)
      wp_pull_exists
      wp_steps
      apply SepWP.focus_rw hout72.symm
      apply SepWP.focus_weaken (kp72_words_fold_memRegion_placed s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8)
      refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by wp_norm_lhs))
        (hnext := ?_)
      have henv_ok0 : CliIdKeyPairPollEnv GetEnv rd s0.fs.files x (w ++ w_1) :=
        SeqEnv.append hget_evs
          (SeqEnv.inl (by simpa [OptIkpTryFromEnv, ← hget_ok.1] using htry_evs))
      refine focus_kpPostPoolPlacedFs FsPost A lim st
        (M.stepEvents w_1 (M.stepEvents w st))
        (CliIdKeyPairPollEnv GetEnv rd s0.fs.files x) (w ++ w_1) x.out
        ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files) ansOk B _ s0
        (hB x.out) hbs72 (by sep_focus)
        (M.stepEvents_append w w_1 st).symm ?_ ?_
      · exact ⟨hans_ok.symm, by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], henv_ok0⟩
      wp_done
    · have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl_sf_1
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hcrl_d0
      wp_call_lscro hDeallocCells hcrl_d0
        ((bPtr, bCap, bs, s0.sp - 176#64), M.stepEvents w_1 (M.stepEvents w st))
      have hfs_sf2 : FsPost sf_2.fs := by
        simpa only [wp_norm, arm64_norm] using ‹FsPost sf_2.fs›
      have h_reg2 : sf_2.sp = s0.sp - 176#64 ∧
          sf_2.readReg64 (.gpr 19#5) = x.fut ∧
          sf_2.readReg64 (.gpr 20#5) = x.out ∧
          sf_2.readReg64 (.gpr 29#5) = s0.sp - 48#64 :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      rcases h_reg2 with ⟨_, _, _, _⟩
      apply sepWP_seg_ls_vm (Q := (blkPC_567).rebase (blkPl_567).base (hooksException H))
        blkLib_eq_567 (mid := s0.readReg64 Reg.lr)
      intro _m_strip
      apply SepWP.focus_weaken (tryFrom_to_idKeyPairOutAt_placed A.repAlloc (s0.sp - 168#64)
        (IdentityKeyPair.tryFrom bs))
      rcases reloc_idKeyPairOutAt A.repAlloc ansOk with ⟨B, hB⟩
      apply SepWP.focus_rw (hB (s0.sp - 168#64))
      wp_pull_exists
      apply SepWP.pure_elim; intro hbs72
      rcases kp72_words_sp168_placed s0.sp x.out hbs72 with
        ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hsp72, hout72⟩
      apply SepWP.focus_rw hsp72
      apply SepWP.focus_rw (memRegion_72_eq_cells9_placed x.out)
      wp_pull_exists
      wp_steps
      apply SepWP.focus_rw hout72.symm
      apply SepWP.focus_weaken (kp72_words_fold_memRegion_placed s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8)
      refine ProofLib.SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by wp_norm_lhs))
        (hnext := ?_)
      have henv_ok1 :
          CliIdKeyPairPollEnv GetEnv rd s0.fs.files x
            (w ++ (w_1 ++ rustDeallocEvents bCap.toNat 1)) :=
        SeqEnv.append hget_evs
          (SeqEnv.append (by simpa [OptIkpTryFromEnv, ← hget_ok.1] using htry_evs)
            (FreeOnlyEvs.singleton 1 bCap.toNat))
      refine focus_kpPostPoolPlacedFs FsPost A lim st
        (M.stepEvents (rustDeallocEvents bCap.toNat 1) (M.stepEvents w_1 (M.stepEvents w st)))
        (CliIdKeyPairPollEnv GetEnv rd s0.fs.files x)
        (w ++ (w_1 ++ rustDeallocEvents bCap.toNat 1)) x.out
        ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files) ansOk B _ s0
        (hB x.out) hbs72 (by sep_focus)
        (by rw [M.stepEvents_append, M.stepEvents_append]) ?_ ?_
      · exact ⟨hans_ok.symm, by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], henv_ok1⟩
      wp_done

/-! ## Two-Sided `withFdsGe3Closed` Outer Contracts (`*_fd`) -/

theorem idKeyPairPollSpecPlaced_mono_env_fd [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PollEnv₁ PollEnv₂ : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {stk : Nat}
    (hsub : ∀ F0 x evs, PollEnv₁ F0 x evs → PollEnv₂ F0 x evs)
    (hok : subroutine_ok prog entry
      (withFdsGe3Closed (idKeyPairPollSpecPlaced rd pathOk A lim PollEnv₁ stk))) :
    subroutine_ok prog entry
      (withFdsGe3Closed (idKeyPairPollSpecPlaced rd pathOk A lim PollEnv₂ stk)) := by
  refine subroutine_ok_mono hok (fun ⟨x, st⟩ R s hp => ?_) (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · obtain ⟨hfds, hp⟩ := extract_withFdsGe3Closed hp
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds, ?_⟩
    unfold idKeyPairPollSpecPlaced at hp ⊢
    obtain ⟨hcrl, hp⟩ := extract_withLsCodeRoLoaded hp
    refine satisfies_lscro_pre hcrl ?_
    dsimp only at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨hx0, hx8, hpath, hpok, hlen, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx8, hpath, hpok, hlen, FitsEnv.mono (hsub s.fs.files x) hfit⟩, hmem⟩
  · obtain ⟨hfds, hq⟩ := extract_withFdsGe3Closed_post hq
    dsimp only [withFdsGe3Closed, idKeyPairPollSpecPlaced, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hans, htr, henv⟩, hmem⟩
    exact ⟨⟨hans, htr, hsub s0.fs.files x evs henv⟩, hmem⟩

set_option maxRecDepth 2000000 in
theorem idKeyPairPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok (lsProg_567 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok (lsProg_567 H) (lsmpl.base 84)
      (withFdsGe3Closed (identityKeyPairTryFromPlacedSpec A lim)))
    (hstk : 0xb0 + kpCalleeStk getStk ≤ stk) :
    subroutine_ok (lsProg_567 H) (lsmpl.base 567)
      (withFdsGe3Closed
        (idKeyPairPollSpecPlaced rd pathOk A lim (CliIdKeyPairPollEnv GetEnv rd) stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [idKeyPairPollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hpath, hpok, hlen, hfit⟩, hmem⟩
  dsimp only [idOwnFutBoxAtPlaced] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64
      (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₈ 0#8) ∗ memRegion (x.fut + 9#64) 7 ∗
        dirAt A.repAlloc x.self x.own ∗ memRegion x.out 72 ∗
        lsLogOff ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    dsimp only [lsLogOff]
    convert hmem using 1; sep_ac_rfl
  let calleeStk := kpCalleeStk getStk
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 176 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 176) (by omega) hstk_hi,
      ProofLib.stackAt_split_cells s0.sp calleeStk 22 hframe_hi] at hmem
  have hro := rodata_idKpFileName_placed hcrl0.2 hmem
  let F_extra :=
    memRegion (x.fut + 9#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 176))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliIdKeyPairPollInnerPlacedSpecFs FdsGe3Closed rd pathOk A lim
          (CliIdKeyPairPollEnv GetEnv rd) calleeStk)).pre (x, st) s0 ∗ (F_extra ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hcrl0 ?_
    dsimp only [cliIdKeyPairPollInnerPlacedSpecFs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfds0, hx0, hx8, hpath, hpok, hlen, hfit⟩, ?_⟩
    dsimp only [F_extra, lsLogOff, CryptoVerification.LibsignalTripleRatchet.lsLogOff] at hro ⊢
    convert hro using 1; sep_ac_rfl
  have hGetCells := dirGetRoFs_cells_placed_ok_fd (calleeStk := calleeStk) hGet
    (by dsimp [calleeStk, kpCalleeStk]; omega) hcal_hi
  have hTryCells := ikpTryFrom_cells_placed_ok_fd (calleeStk := calleeStk) hDec
    (by dsimp [calleeStk, kpCalleeStk]; omega) hcal_hi
  have hDeallocCells := deallocAt_cells_placed_ok_fd (prog := lsProg_567 H)
    (calleeStk := calleeStk) hC (by decide)
    (by dsimp [calleeStk, kpCalleeStk]; omega) hcal_hi
  refine (idKeyPairPollInner_fsPost_placed_ok (fun _ h => h) hGetCells hTryCells hDeallocCells).mono_outcome
    (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpecFs, withFdsGe3Closed,
      idKeyPairPollSpecPlaced, idOwnFutBoxAtPlaced, kpPostPoolPlacedFs] at hq ⊢
    simp_rw [idKeyPairOutAtPlaced_eq]
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨evs, ans, hq⟩
    have hq_pure : sf.mem ⊨
        ⌜ans = (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files ∧
          sf.trace = s0.trace ∧ FdsGe3Closed sf.fs ∧
          CliIdKeyPairPollEnv GetEnv rd s0.fs.files x evs⌝ ∗
        ((lsρ idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
          (idKeyPairOutAt A.repAlloc x.out ans ∗
            ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗ memRegion (x.fut + 9#64) 7) ∗
            dirAt A.repAlloc x.self x.own ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 176)) ∗
              (stackAt (s0.sp - 176#64) calleeStk ∗ cells (s0.sp - 176#64) 22))) ∗ R) := by
      dsimp only [F_extra] at hq
      exact Satisfies.mono (by sep_focus) hq
    rw [satisfies_pure_sepConj] at hq_pure
    rcases hq_pure with ⟨⟨hans, htr, hfdsf, henv⟩, hq_ro⟩
    have hq_drop := Satisfies.of_sep_right hq_ro
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ans, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 176) (by omega) hstk_hi,
        ProofLib.stackAt_split_cells s0.sp calleeStk 22 hframe_hi]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hans, htr, henv⟩, ?_⟩
    dsimp only [lsLogOff, CryptoVerification.LibsignalTripleRatchet.lsLogOff] at hq_drop ⊢
    rw [show BitVec.ofNat 64 (8 * 22) = 176#64 from rfl]
    convert hq_drop using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [cliIdKeyPairPollInnerPlacedSpecFs, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem idKeyPairPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg decProg : Program} {callerBlk getBlk decBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 84)
      (withFdsGe3Closed (identityKeyPairTryFromPlacedSpec A lim)))
    (hstk : 0xb0 + kpCalleeStk getStk ≤ stk)
    (hblk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 567)
      (withFdsGe3Closed
        (idKeyPairPollSpecPlaced rd pathOk A lim (CliIdKeyPairPollEnv GetEnv rd) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 567)
    (idKeyPairPoll_placed_ok_of_deps_fd hC
      (ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_567 H) (j := getBlk)
        hGet (by decide) hGetBlk hGetUnmut)
      (ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_567 H) (j := decBlk)
        hDec (by decide) hDecBlk hDecUnmut)
      hstk)
    hblk

/-- CLI instantiation of `IdentityFiles::get_identity_key_pair::{closure#0}` (Block `567`)
with two-sided `withFdsGe3Closed` at residual stack `stk - cliInitiateFrame`. -/
theorem idKeyPairPoll_cli_placed_ok_fd [LibsignalPlacement] {prog getProg decProg : Program}
    {i getBlk decBlk : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    [IsLsBlockProg prog i H] [IsLsBlockProg getProg getBlk H] [IsLsBlockProg decProg decBlk H]
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    (B : RunBudgets)
    (hC : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced cliIo.rd cliWrOk A lim GetEnv B.dirGetNeed)))
    (hDec : subroutine_ok decProg (lsmpl.base 84)
      (withFdsGe3Closed (identityKeyPairTryFromPlacedSpec A lim)))
    (hi : i < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok prog (lsmpl.base 567)
      (withFdsGe3Closed
        (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A lim (CliIdKeyPairPollEnv GetEnv cliIo.rd)
          (stk - cliInitiateFrame))) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hs : smallRootStack ≤ 65536 := by decide
  have he : extHookStack ≤ 65536 := by decide
  exact idKeyPairPoll_placed_caller_ok_of_deps_fd hC hGet hDec
    (by dsimp only [kpCalleeStk]; omega) hi hGetBlk hGetUnmut hDecBlk hDecUnmut

/-! ## Pre-Only `FdsGe3Closed` Outer Contracts (`*_preFd`) -/

set_option maxRecDepth 2000000 in
theorem idKeyPairPoll_preFd_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok (lsProg_567 H) (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok (lsProg_567 H) (lsmpl.base 84)
      (identityKeyPairTryFromPlacedSpec A lim))
    (hstk : 0xb0 + kpCalleeStk getStk ≤ stk) :
    subroutine_ok (lsProg_567 H) (lsmpl.base 567)
      (withPreGuard (fun s => FdsGe3Closed s.fs)
        (idKeyPairPollSpecPlaced rd pathOk A lim (CliIdKeyPairPollEnv GetEnv rd) stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withPreGuard] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hfds0, hpre⟩ := hpre
  obtain ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [idKeyPairPollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hpath, hpok, hlen, hfit⟩, hmem⟩
  dsimp only [idOwnFutBoxAtPlaced] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64
      (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₈ 0#8) ∗ memRegion (x.fut + 9#64) 7 ∗
        dirAt A.repAlloc x.self x.own ∗ memRegion x.out 72 ∗
        lsLogOff ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    dsimp only [lsLogOff]
    convert hmem using 1; sep_ac_rfl
  let calleeStk := kpCalleeStk getStk
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 176 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 176) (by omega) hstk_hi,
      ProofLib.stackAt_split_cells s0.sp calleeStk 22 hframe_hi] at hmem
  have hro := rodata_idKpFileName_placed hcrl0.2 hmem
  let F_extra :=
    memRegion (x.fut + 9#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 176))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliIdKeyPairPollInnerPlacedSpecFs (fun _ => True) rd pathOk A lim
          (CliIdKeyPairPollEnv GetEnv rd) calleeStk)).pre (x, st) s0 ∗ (F_extra ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hcrl0 ?_
    dsimp only [cliIdKeyPairPollInnerPlacedSpecFs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfds0, hx0, hx8, hpath, hpok, hlen, hfit⟩, ?_⟩
    dsimp only [F_extra, lsLogOff, CryptoVerification.LibsignalTripleRatchet.lsLogOff] at hro ⊢
    convert hro using 1; sep_ac_rfl
  have hGetCells := dirGetRoFs_cells_placed_ok_fd (calleeStk := calleeStk) hGet
    (by dsimp [calleeStk, kpCalleeStk]; omega) hcal_hi
  have hTryCells := subroutine_ok_lscro_withFsPred_true
    (ikpTryFrom_cells_placed_ok (calleeStk := calleeStk) hDec
      (by dsimp [calleeStk, kpCalleeStk]; omega) hcal_hi)
  have hDeallocCells := subroutine_ok_lscro_withFsPred_true
    (deallocAt_cells_placed_ok (prog := lsProg_567 H) (calleeStk := calleeStk) hC (by decide)
      (by dsimp [calleeStk, kpCalleeStk]; omega) hcal_hi)
  refine (idKeyPairPollInner_fsPost_placed_ok (fun _ _ => trivial)
    hGetCells hTryCells hDeallocCells).mono_outcome
    (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpecFs, withPreGuard,
      idKeyPairPollSpecPlaced, idOwnFutBoxAtPlaced, kpPostPoolPlacedFs] at hq ⊢
    simp_rw [idKeyPairOutAtPlaced_eq]
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    have hq_pure : sf.mem ⊨
        ⌜ans = (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files ∧
          sf.trace = s0.trace ∧ True ∧
          CliIdKeyPairPollEnv GetEnv rd s0.fs.files x evs⌝ ∗
        ((lsρ idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
          (idKeyPairOutAt A.repAlloc x.out ans ∗
            ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗ memRegion (x.fut + 9#64) 7) ∗
            dirAt A.repAlloc x.self x.own ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 176)) ∗
              (stackAt (s0.sp - 176#64) calleeStk ∗ cells (s0.sp - 176#64) 22))) ∗ R) := by
      dsimp only [F_extra] at hq
      exact Satisfies.mono (by sep_focus) hq
    rw [satisfies_pure_sepConj] at hq_pure
    rcases hq_pure with ⟨⟨hans, htr, _, henv⟩, hq_ro⟩
    have hq_drop := Satisfies.of_sep_right hq_ro
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 176) (by omega) hstk_hi,
        ProofLib.stackAt_split_cells s0.sp calleeStk 22 hframe_hi]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hans, htr, henv⟩, ?_⟩
    dsimp only [lsLogOff, CryptoVerification.LibsignalTripleRatchet.lsLogOff] at hq_drop ⊢
    rw [show BitVec.ofNat 64 (8 * 22) = 176#64 from rfl]
    convert hq_drop using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpecFs] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [cliIdKeyPairPollInnerPlacedSpecFs, withLsCodeRoLoaded] at hq
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

theorem idKeyPairPoll_preFd_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg decProg : Program} {callerBlk getBlk decBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 84)
      (identityKeyPairTryFromPlacedSpec A lim))
    (hstk : 0xb0 + kpCalleeStk getStk ≤ stk)
    (hblk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 567)
      (withPreGuard (fun s => FdsGe3Closed s.fs)
        (idKeyPairPollSpecPlaced rd pathOk A lim (CliIdKeyPairPollEnv GetEnv rd) stk)) :=
  ls_transfer_preFd_lscro (callerProg := callerProg) (j := 567)
    (idKeyPairPoll_preFd_placed_ok_of_deps hC
      (ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_567 H) (j := getBlk)
        hGet (by decide) hGetBlk hGetUnmut)
      (ls_transfer_lscro (callerProg := lsProg_567 H) (j := decBlk)
        hDec (by decide) hDecBlk hDecUnmut)
      hstk)
    hblk

/-- Pre-only `FdsGe3Closed` CLI instantiation of `IdentityFiles::get_identity_key_pair::{closure#0}`
(Block `567`) directly from `RunHooksPlaced` (`hh.identityKeyPair_tryFrom_placed_ok`) and
`withFdsGe3Closed (dirGetSpecPlaced …)`. -/
theorem idKeyPairPoll_cli_preFd_placed_ok [LibsignalPlacement] {prog getProg : Program}
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
    subroutine_ok prog (lsmpl.base 567)
      (withPreGuard (fun s => FdsGe3Closed s.fs)
        (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A lim (CliIdKeyPairPollEnv GetEnv cliIo.rd)
          (stk - cliInitiateFrame))) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hs : smallRootStack ≤ 65536 := by decide
  have he : extHookStack ≤ 65536 := by decide
  exact idKeyPairPoll_preFd_placed_caller_ok_of_deps hh.alloc hGet
    hh.identityKeyPair_tryFrom_placed_ok
    (by dsimp only [kpCalleeStk]; omega) hi hGetBlk hGetUnmut

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudgetFd
