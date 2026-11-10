/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPoll
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# `IdentityFiles::get_local_registration_id::{closure#0}` (`[LibsignalPlacement]`, Block `568`)

Verifies `idRegIdPoll_placed_ok_of_deps` on `lsProg_568 H` and `idRegIdPoll_cli_placed_ok` against
`idRegIdPollSpecPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
  withLsCodeRoLoaded extract_withLsCodeRoLoaded
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll.RegNorm

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
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
  awc_speWord1_two awc_okTagVec_two RegNorm.truncate32_zeroExtend64

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
  awc_speWord1_two awc_okTagVec_two RegNorm.truncate32_zeroExtend64

/-! ## Cell-Oriented Callee Wrappers -/

private theorem reg568_dirGet_target [LibsignalPlacement] :
    (blkPl_568).ρ dirGetName = lsmpl.base 589 := by
  simp only [arm64_norm]

theorem shimAt_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (shimCellsSpec calleeStk)) := by
  have hShim : subroutine_ok prog (lsρ lsRustNoAllocShimSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (withStack sessionShimSpec calleeStk)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := prog) (hC.shim calleeStk hle hhi) hi
  intro fsp R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsRoCl hpre
  simp only [shimCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfsp, hmem⟩
  subst hfsp
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (withStack sessionShimSpec calleeStk)).pre () s0 ∗ R := by
    refine satisfies_withLsRoCl_pre hcrl0 ?_
    dsimp only [withStack, sessionShimSpec]
    rw [emp_sepConj]
    exact hmem
  rcases hShim () R s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, withStack, sessionShimSpec,
      shimCellsSpec] at hq ⊢
    exact hq
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, withStack, sessionShimSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, withStack, sessionShimSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, withStack, sessionShimSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem alloc14At_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustAllocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (alloc14CellsSpec A calleeStk)) := by
  have hAlloc : subroutine_ok prog (lsρ lsRustAllocSymCli)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (rustAllocSpecWithStack A extHookStack)) :=
    ls_subroutine_ok_rocl_of_block (callerProg := prog) hC.alloc hi
  intro fsp R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsRoCl hpre
  simp only [alloc14CellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi] at hmem
  have hlay : LayoutOk 14 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hpre0 : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (rustAllocSpecWithStack A extHookStack)).pre (14, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_withLsRoCl_pre hcrl0 ?_
    dsimp only [rustAllocSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by rw [hx0]; rfl, by rw [hx1]; rfl, hlay⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hAlloc (14, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustAllocSpecWithStack,
      alloc14CellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hcrlf, hq⟩
    refine ⟨hcrlf, ?_⟩
    by_cases hr0 : sf.readReg64 .x0 = 0#64
    · have hr0' : sf.readReg64 .x0 = (0 : BitVec 64) := hr0
      simp only [hr0', ite_true] at hq
      simp only [hr0, ite_true]
      rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
    · have hr0' : sf.readReg64 .x0 ≠ (0 : BitVec 64) := hr0
      have hmod : (((sf.readReg64 .x0).toNat % 1 = 0 ∧ sf.trace = s0.trace) : Prop) =
          (sf.trace = s0.trace) := by
        simp [Nat.mod_one]
      simp only [hr0', ite_false, hmod] at hq
      simp only [hr0, ite_false]
      rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp hle hhi]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustAllocSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustAllocSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl, rustAllocSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## Inner Specification and Symbolic Execution (Block `568`) -/

private def cliIdRegIdPollInnerPlacedSpec [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (w0 wTail : BitVec 64) (calleeStk : Nat) :
    Spec IdOwnPollGhostPlaced where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
      (lsρ PollCommon.idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ PollCommon.malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ PollCommon.malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A x.self x.own ∗
      memRegion x.out 48 ∗ A.pool ∗
      stackAt (s.sp - 112#64) calleeStk ∗ cells (s.sp - 112#64) 14
  post := fun x s0 sf =>
    regPostAns A x.out ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) s0 sf ∗
      (lsρ PollCommon.idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ PollCommon.malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ PollCommon.malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A x.self x.own ∗
      A.pool ∗
      stackAt (s0.sp - 112#64) calleeStk ∗ cells (s0.sp - 112#64) 14
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def cliIdRegIdPollExpandedPlacedSpec [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (w0 wTail : BitVec 64) (calleeStk : Nat) :
    Spec IdOwnPollGhostPlaced where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "registration-id"))⌝ ∗
      (lsρ PollCommon.idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ PollCommon.malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ PollCommon.malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A x.self x.own ∗
      memRegion x.out 48 ∗ A.pool ∗
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
  post := fun x s0 sf =>
    regPostAns A x.out ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files) s0 sf ∗
      (lsρ PollCommon.idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
      (lsρ PollCommon.malformedFileStrSym ↦₆₄ᵣ w0) ∗
      ((lsρ PollCommon.malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A x.self x.own ∗
      A.pool ∗
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
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem cliIdRegIdPollExpandedPlacedSpec_eq [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (w0 wTail : BitVec 64) (calleeStk : Nat) :
    cliIdRegIdPollExpandedPlacedSpec rd pathOk A w0 wTail calleeStk =
      cliIdRegIdPollInnerPlacedSpec rd pathOk A w0 wTail calleeStk := by
  unfold cliIdRegIdPollExpandedPlacedSpec cliIdRegIdPollInnerPlacedSpec
  congr 1
  · funext x s; rw [cells_14_reg s.sp]
  · funext x s0 sf; rw [cells_14_reg s0.sp]

set_option maxHeartbeats 1200000 in
private theorem idRegIdPollInner_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {w0 wTail : BitVec 64} {getStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hPanicRaw : H "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hGet : subroutine_ok (lsProg_568 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk))
    (hhi : regCalleeStk getStk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_568 H) (blkPl_568).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (cliIdRegIdPollInnerPlacedSpec rd pathOk A w0 wTail (regCalleeStk getStk))) := by
  let calleeStk := regCalleeStk getStk
  rw [← cliIdRegIdPollExpandedPlacedSpec_eq]
  have hGetCells : subroutine_ok (lsProg_568 H) ((blkPl_568).ρ dirGetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (PollCommon.dirGetRoCellsSpec rd pathOk A calleeStk)) :=
    reg568_dirGet_target.symm ▸ PollCommon.dirGetRo_cells_placed_ok (calleeStk := calleeStk)
      (subroutine_ok_rocl_of_withLsCodeRoLoaded hGet)
      (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hDeallocCells := PollCommon.deallocAt_cells_placed_ok (prog := lsProg_568 H)
    (calleeStk := calleeStk) hC (by decide)
    (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hShimCells := shimAt_cells_placed_ok (prog := lsProg_568 H) (calleeStk := calleeStk) hC
    (by decide) (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hAllocCells := alloc14At_cells_placed_ok (prog := lsProg_568 H) (calleeStk := calleeStk) hC
    (by decide) (by dsimp [calleeStk, regCalleeStk]; omega) hhi
  have hPanic : ((blkPC_568).rebase (blkPl_568).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked :=
    (ls_externAt?_of_mem
      (sym := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")).trans hPanicRaw
  dsimp only [lsProg_568, ite_true] at hGetCells hDeallocCells hShimCells hAllocCells ⊢
  clear hGet hC hPanicRaw
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  simp (config := { maxSteps := 2000000 }) only [cliIdRegIdPollExpandedPlacedSpec,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hname_len : (utf8 "registration-id").length = 15 := PollCommon.utf8_regId_length
  have hname_lt : (utf8 "registration-id").length < 2 ^ 32 := by
    rw [PollCommon.utf8_regId_length]; decide
  apply sepWPp_of_sepWP_lscro hcrl0 (mid := (blkPl_568).ρ dirGetName)
  wp_steps
  apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro hGetCells hcrl1
    (s0.sp - 112#64, x.self, x.own,
      lsρ PollCommon.idRegIdFileNameSym, utf8 "registration-id", s0.sp - 112#64)
  case panic =>
    intro sf_p _ hm
    dsimp only at hm
    exact close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
  have h_reg0 : sf.sp = s0.sp - 112#64 ∧
      sf.readReg64 (.gpr 19#5) = x.fut ∧
      sf.readReg64 (.gpr 20#5) = x.out ∧
      sf.readReg64 (.gpr 29#5) = s0.sp - 64#64 :=
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  rcases h_reg0 with ⟨_, _, _, _⟩
  cases w with
  | error u =>
    cases u
    have hget_err : .error () = x.own.get rd s0.fs.files (utf8 "registration-id") ∧
        sf.trace = s0.trace := ⟨by assumption, by assumption⟩
    have hans_err : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files = .error () := by
      unfold IdGhost.regId
      rw [← hget_err.1]
      rfl
    apply SepWPp.of_sepWP_ret
    apply SepWP.focus_rw (getResultAt_err_sp_112 A s0.sp)
    wp_pull_exists
    apply SepWP.focus_rw (out_48_reg_split x.out)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_weaken (sp_112_err_fold_48 s0.sp _ _ _ _ _ _ _)
    apply SepWP.focus_weaken (out_reg_err_read_fold A x.out _ _ _ _)
    refine focus_regPostAns A x.out
      ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
      (.error ()) s0 (by sep_focus) ?_ ?_
    · exact ⟨hans_err.symm, by simp only [wp_norm, arm64_norm, *]⟩
    wp_done
  | ok bs =>
    have hget_ok : .ok bs = x.own.get rd s0.fs.files (utf8 "registration-id") ∧
        sf.trace = s0.trace := ⟨by assumption, by assumption⟩
    rw [getResultAt_ok_sp_112 A s0.sp bs]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bCap
    apply SepWPp.exists_elim; intro bPtr
    apply SepWPp.pure_elim; rintro ⟨hbCap_le, hbCap_lt, hbPtr_ne⟩
    by_cases hlen4 : bs.length = 4
    · match bs, hlen4 with
      | [b0, b1, b2, b3], _ =>
        have hans_ok : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files =
            .ok (b3 ++ b2 ++ b1 ++ b0) := by
          unfold IdGhost.regId
          rw [← hget_ok.1]
          rfl
        have hbCap_ne : bCap ≠ 0#64 :=
          Store.IdTrustPoll.Helpers.cap_ne_zero_of_cons hbCap_le
        have hbCap_beq : (bCap == 0#64) = false := beq_false_of_ne hbCap_ne
        apply sepWPp_of_sepWP_lscro hcrl_sf (mid := lsρ lsRustDeallocSymCli)
        apply SepWP.focus_rw (pointsToBytes4_eq_pointsTo32 bPtr b0 b1 b2 b3)
        wp_steps
        apply SepWP.focus_rw (pointsToBytes4_eq_pointsTo32 bPtr b0 b1 b2 b3).symm
        apply SepWP.focus_weaken (sp_112_ok_fold_48 s0.sp _ _ _ _ _)
        apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        intro hcrl_d0
        wp_call_lscro hDeallocCells hcrl_d0 (bPtr, bCap, [b0, b1, b2, b3], s0.sp - 112#64)
        case panic =>
          intro sf_p _ hm
          dsimp only at hm
          simpa only [sepConj_assoc] using
            close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
        have h_reg_b2 : sf_1.sp = s0.sp - 112#64 ∧
            sf_1.readReg64 (.gpr 19#5) = x.fut ∧
            sf_1.readReg64 (.gpr 20#5) = x.out ∧
            sf_1.readReg64 (.gpr 22#5) = (b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 :=
          ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
        rcases h_reg_b2 with ⟨_, _, _, _⟩
        apply SepWPp.of_sepWP_ret
        apply SepWP.focus_rw (out_48_reg_split x.out)
        wp_pull_exists
        wp_steps
        apply SepWP.focus_weaken (out_reg_ok_fold A x.out (b3 ++ b2 ++ b1 ++ b0) _ _ _ _ _)
        refine focus_regPostAns A x.out
          ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
          (.ok (b3 ++ b2 ++ b1 ++ b0)) s0 (by sep_focus) ?_ ?_
        · exact ⟨hans_ok.symm, by simp only [wp_norm, arm64_norm, *]⟩
        wp_done
    · have hans_err4 : (IdGhost.mk x.own (.new [])).regId rd s0.fs.files = .error () := by
        unfold IdGhost.regId
        rw [← hget_ok.1]
        exact match_regId_ne_4 hlen4
      have hlen_lt : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hbCap_le hbCap_lt
      have hne4_bv : BitVec.ofNat 64 bs.length ≠ 4#64 := len_bv_ne_four_of_ne hlen_lt hlen4
      have hne4_beq : (BitVec.ofNat 64 bs.length == 4#64) = false := beq_false_of_ne hne4_bv
      have hne4_sub : (BitVec.ofNat 64 bs.length - 4#64 == 0#64) = false :=
        beq_false_of_ne (fun h => hne4_bv (by bv_omega))
      have hne4_awc : (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~4#64) true).2.z = false := by
        unfold AddWithCarry64
        simp only [ite_true]
        exact beq_false_of_ne (fun h => hne4_bv (by bv_omega))
      apply sepWPp_of_sepWP_lscro hcrl_sf (mid := lsρ lsRustNoAllocShimSymCli)
      wp_steps
      apply SepWP.focus_weaken (sp_112_ok_fold_48 s0.sp _ _ _ _ _)
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hcrl_s
      wp_call_lscro hShimCells hcrl_s (s0.sp - 112#64)
      case panic =>
        intro sf_p _ hm
        dsimp only at hm
        simpa only [sepConj_assoc] using
          close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
      have h_reg_s : sf_1.sp = s0.sp - 112#64 ∧
          sf_1.readReg64 (.gpr 19#5) = x.fut ∧
          sf_1.readReg64 (.gpr 20#5) = x.out ∧
          sf_1.readReg64 (.gpr 21#5) = bPtr ∧
          sf_1.readReg64 (.gpr 23#5) = bCap :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩
      rcases h_reg_s with ⟨_, _, _, _, _⟩
      apply sepWPp_of_sepWP_lscro hcrl_sf_1 (mid := lsρ lsRustAllocSymCli)
      wp_steps
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hcrl_a
      wp_call_lscro hAllocCells hcrl_a (s0.sp - 112#64)
      case panic =>
        intro sf_p _ hm
        dsimp only at hm
        simpa only [sepConj_assoc] using
          close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
      have h_reg_a : sf_2.sp = s0.sp - 112#64 ∧
          sf_2.readReg64 (.gpr 19#5) = x.fut ∧
          sf_2.readReg64 (.gpr 20#5) = x.out ∧
          sf_2.readReg64 (.gpr 21#5) = bPtr ∧
          sf_2.readReg64 (.gpr 23#5) = bCap :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩
      rcases h_reg_a with ⟨_, _, _, _, _⟩
      by_cases hbuf0 : sf_2.readReg64 (.gpr 0#5) = 0#64
      · have hbuf0' : sf_2.readReg64 .x0 = 0#64 := hbuf0
        simp only [hbuf0', ite_true]
        rw [← sepConj_assoc, sepConj_comm (A.pool ∗ stackAt (s0.sp - 112#64) calleeStk), sepConj_assoc]
        apply SepWPp.pure_elim; intro htr_oom
        apply SepWPp.of_sepWP
          (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
        wp_steps
        apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
        refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked
            (LibsignalTripleRatchet.allocFailedIn_of_eq
              (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
      · have hbuf_ne : sf_2.readReg64 .x0 ≠ 0#64 := hbuf0
        have hbuf_beq : (sf_2.readReg64 (.gpr 0#5) == 0#64) = false := beq_false_of_ne hbuf0
        simp only [hbuf_ne, ite_false]
        rw [← sepConj_assoc, sepConj_comm (A.pool ∗ stackAt (s0.sp - 112#64) calleeStk), sepConj_assoc]
        simp only [sepConj_assoc]
        apply SepWPp.pure_elim; intro htr_alloc
        by_cases hc0 : bCap = 0#64
        · subst hc0
          have hbs_nil : bs = [] := by
            cases bs with
            | nil => rfl
            | cons _ _ => simp at hbCap_le
          subst hbs_nil
          apply SepWPp.of_sepWP_ret
          have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗
              Store.IdTrustPoll.Helpers.vecU8BufRest A 0#64 bPtr 0) = emp := by
            simp [Store.IdTrustPoll.Helpers.vecU8BufRest]
          apply SepWP.focus_rw hemp
          apply SepWP.focus_rw (PollCommon.memRegion_14_split_8_6 (sf_2.readReg64 .x0))
          wp_pull_exists
          apply SepWP.focus_rw (out_48_reg_split x.out)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_mid (sf_2.readReg64 .x0) w0)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_done (sf_2.readReg64 .x0) w0 wTail)
          apply SepWP.focus_weaken
            (out_reg_err_malformed_fold A x.out (sf_2.readReg64 .x0) _ _
              ((unpack64 w0).take 6 ++ unpack64 wTail)
              hbuf_ne (PollCommon.write_14_overlap_length w0 wTail))
          refine focus_regPostAns A x.out
            ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
            (.error ()) s0 (by sep_focus) ?_ ?_
          · exact ⟨hans_err4.symm, by simp only [wp_norm, arm64_norm, *]⟩
          wp_done
        · have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
          apply sepWPp_of_sepWP_lscro hcrl_sf_2 (mid := lsρ lsRustDeallocSymCli)
          apply SepWP.focus_rw (PollCommon.memRegion_14_split_8_6 (sf_2.readReg64 .x0))
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_mid (sf_2.readReg64 .x0) w0)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken (PollCommon.write_14_overlap_done (sf_2.readReg64 .x0) w0 wTail)
          apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
          intro hcrl_d1
          wp_call_lscro hDeallocCells hcrl_d1 (bPtr, bCap, bs, s0.sp - 112#64)
          case panic =>
            intro sf_p _ hm
            dsimp only at hm
            simpa only [sepConj_assoc] using
              close_panic_subgoal s0 hm (by simp only [wp_norm, arm64_norm, *])
          have h_reg_d : sf_3.sp = s0.sp - 112#64 ∧
              sf_3.readReg64 (.gpr 19#5) = x.fut ∧
              sf_3.readReg64 (.gpr 20#5) = x.out ∧
              sf_3.readReg64 (.gpr 22#5) = sf_2.readReg64 .x0 :=
            ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
          rcases h_reg_d with ⟨_, _, _, _⟩
          apply SepWPp.of_sepWP_ret
          apply SepWP.focus_rw (out_48_reg_split x.out)
          wp_pull_exists
          wp_steps
          apply SepWP.focus_weaken
            (out_reg_err_malformed_fold A x.out (sf_2.readReg64 .x0) _ _
              ((unpack64 w0).take 6 ++ unpack64 wTail)
              hbuf_ne (PollCommon.write_14_overlap_length w0 wTail))
          refine focus_regPostAns A x.out
            ((IdGhost.mk x.own (.new [])).regId rd s0.fs.files)
            (.error ()) s0 (by sep_focus) ?_ ?_
          · exact ⟨hans_err4.symm, by simp only [wp_norm, arm64_norm, *]⟩
          wp_done

/-! ## Outer Wrapper and CLI Instantiation -/

set_option maxRecDepth 2000000 in
theorem idRegIdPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hPanicRaw : H "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked)
    (hGet : subroutine_ok (lsProg_568 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk))
    (hstk : 0x70 + regCalleeStk getStk ≤ stk) :
    subroutine_ok (lsProg_568 H) (lsmpl.base 568)
      (idRegIdPollSpecPlaced rd pathOk A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [idRegIdPollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hpath, hpok⟩, hmem⟩
  dsimp only [idOwnFutBoxAtPlaced] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine Store.IdTrustPoll.Helpers.memRegion_bound_of_pointsTo64
      (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₈ 0#8) ∗ memRegion (x.fut + 9#64) 7 ∗
        dirAt A x.self x.own ∗ memRegion x.out 48 ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  let calleeStk := regCalleeStk getStk
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 112 ≤ 2 ^ 64 := by omega
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp (subStk := calleeStk + 112)
        (by omega) hstk_hi,
      ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi] at hmem
  obtain ⟨w0, wTail, hro⟩ := PollCommon.rodata_regId_and_malformed_placed hcrl0.2 hmem
  let F_extra :=
    memRegion (x.fut + 9#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112))
  have hpre_in : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (cliIdRegIdPollInnerPlacedSpec rd pathOk A w0 wTail calleeStk)).pre x s0 ∗ (F_extra ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hcrl0 ?_
    dsimp only [cliIdRegIdPollInnerPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hpath, hpok⟩, ?_⟩
    dsimp only [F_extra]
    exact Satisfies.mono (by sep_focus) hro
  rcases idRegIdPollInner_placed_ok (w0 := w0) (wTail := wTail) hC hPanicRaw hGet hcal_hi x
      (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpec,
      idRegIdPollSpecPlaced, idOwnFutBoxAtPlaced, regPostAns] at hq ⊢
    simp_rw [PollCommon.idRegIdOutAtPlaced_eq]
    have hq_ro : sf.mem ⊨
        ((lsρ PollCommon.idRegIdFileNameSym ↦ᵣ utf8 "registration-id") ∗
          (lsρ PollCommon.malformedFileStrSym ↦₆₄ᵣ w0) ∗
          ((lsρ PollCommon.malformedFileStrSym + 6#64) ↦₆₄ᵣ wTail)) ∗
        (((∃∗ ans : Except Unit (BitVec 32),
            ⌜ans = (IdGhost.mk x.own (.new [])).regId rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
            idRegIdOutAt A x.out ans) ∗
          ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗ memRegion (x.fut + 9#64) 7) ∗
          dirAt A x.self x.own ∗ A.pool ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 112)) ∗
            (stackAt (s0.sp - 112#64) calleeStk ∗ cells (s0.sp - 112#64) 14))) ∗ R) := by
      dsimp only [F_extra] at hq
      exact Satisfies.mono (by sep_focus) hq
    have hq_drop := Satisfies.of_sep_right hq_ro
    rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp (subStk := calleeStk + 112)
          (by omega) hstk_hi,
        ProofLib.stackAt_split_cells s0.sp calleeStk 14 hframe_hi]
    exact hq_drop
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cliIdRegIdPollInnerPlacedSpec,
      idRegIdPollSpecPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      cliIdRegIdPollInnerPlacedSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      cliIdRegIdPollInnerPlacedSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- CLI instantiation of `IdentityFiles::get_local_registration_id::{closure#0}` (Block `568`)
transferred onto any caller block program `prog` (e.g. `initProgPlaced W`). -/
theorem idRegIdPoll_cli_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {W : CliHooks} {H : LibsignalHooks} [IsLsBlockProg prog i H] (B : RunBudgets)
    (hh : RunHooksPlaced W A H)
    (hGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A B.dirGetNeed))
    (hi : i < 619 := by decide)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok prog (lsmpl.base 568)
      (idRegIdPollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have he : extHookStack ≤ 65536 := by decide
  have hGet568 : subroutine_ok (lsProg_568 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A B.dirGetNeed) := by
    have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := lsProg_568 H) hGet
    exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
          LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  have h568 := idRegIdPoll_placed_ok_of_deps (stk := stk - cliInitiateFrame)
    hh.alloc hh.panic_raw hGet568 (by dsimp only [regCalleeStk]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := prog) h568 hi
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
        LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdRegIdPoll
