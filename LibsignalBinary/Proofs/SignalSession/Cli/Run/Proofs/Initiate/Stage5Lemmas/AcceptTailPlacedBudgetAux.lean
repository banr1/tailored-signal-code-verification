/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Stage 5 Accept Path Segment Helpers (`[LibsignalPlacement]`)

Minimal-frame segment proofs for `save_identity` (`+0x163c..+0x1730`) and `memcpy` +
`promote_state` (`+0x1734..+0x1764`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudgetAux

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli hiding
  idSaveShimSpecPlaced idSavePollSpecPlaced sessStoreShimSpecPlaced sessStorePollSpecPlaced
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (sepWPp_weaken_pre sepWPp_pure_left sepWPp_exists_left)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas hiding
  s5_call_raw_placed s5_dealloc_ok_at_placed s5_memcpy_ok_at_placed s5_call_futDrop_placed
  s5_call_dealloc_placed s5_call_dropSS_placed s5_call_idSaveShim_placed s5_call_idSavePoll_placed
  s5_call_memcpy_placed s5_call_promoteState_placed s5_call_sessStoreShim_placed
  s5_call_sessStorePoll_placed stage5_epilogue_placed_ok stage5_err_cleanup_placed_ok
  stage5_cleanup_after_store_placed_ok stage5_store_and_cleanup_placed_ok stage5_accept_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced idSaveShimSpecPlaced idSavePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
  (s5_call_futDrop_pool_placed s5_call_dealloc_placed s5_dealloc_ok_at_placed s5_memcpy_ok_at_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec s5_call_idSaveShim_placed s5_call_idSavePoll_placed
   s5_call_memcpy_pool_placed s5_call_promoteState_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
  (sepWPp_step_to_lscro_vm_mem_framed)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm, -wp_norm] fsp_stage5_eqs
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

@[local arm64_norm, local wp_norm]
private theorem fsp_compound_offs_placed (fsp : BitVec 64) :
    fsp + 0xe0#64 + 8#64 = fsp + 0xe8#64 ∧ fsp + 0xf0#64 + 8#64 = fsp + 0xf8#64 ∧
    fsp + 0xf8#64 + 8#64 = fsp + 0x100#64 ∧ fsp + 0x100#64 + 8#64 = fsp + 0x108#64 ∧
    fsp + 0x80#64 + 168#64 = fsp + 0x128#64 ∧ fsp + 0x80#64 + 192#64 = fsp + 0x140#64 ∧
    fsp + 0x80#64 + 536#64 = fsp + 0x298#64 ∧ fsp + 0x460#64 + 0x154#64 = fsp + 0x5b4#64 ∧
    fsp + 4096#64 + 1536#64 = fsp + 0x1600#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
   by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

private theorem sepWP_done_tpidr {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0) (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

private theorem s5_apply_lens_oom {prog : Program} {ret : BitVec 64} {s : State}
    {L P Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (heq : P = L ∗ Rest)
    (h : ∀ R (m : Memory), m ⊨ L ∗ R → ∃ B : SepProp, m ⊨ B ∗ R ∧
      SepWPp prog ret s (B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rw [heq, sepConj_assoc] at hm
  obtain ⟨B, hmB, hw⟩ := h (Rest ∗ R) s.mem hm
  rw [← sepConj_assoc] at hmB
  exact hw R hmB hL

private theorem s5_with_rodata_oom {prog : Program} {ret : BitVec 64} {s : State}
    {RO P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : ∀ {X : SepProp}, s.mem ⊨ X → s.mem ⊨ (RO ∗ X))
    (hw : SepWPp prog ret s (RO ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hw R (by rw [sepConj_assoc]; exact hro hm) hL

/-! ## Minimal-Frame Decomposition -/

def initArgsSaveRestPlaced [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) : SepProp :=
  ((fsp + 0xd8#64) ↦₆₄ x.meA) ∗
    ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
    ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym) ∗
    ((fsp + 0x108#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (fsp + 0x114#64) 4 ∗
    ((fsp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64))

theorem initArgsAtPlaced_save_split [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) :
    initArgsAtPlaced fsp x s0 =
      (((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
        ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64))) ∗
      initArgsSaveRestPlaced fsp x s0 := by
  dsimp only [initArgsAtPlaced, initArgsSaveRestPlaced]; ac_rfl

def stage5ScratchSaveRestPlaced (fsp w5d0 : BitVec 64) : SepProp :=
  memRegion (fsp + 0x5ba#64) 6 ∗
    ((fsp + 0x5d0#64) ↦₆₄ w5d0) ∗
    memRegion (fsp + 0x5d8#64) (0x1600 - 0x5d8) ∗
    memRegion (fsp + 0x1630#64) 296 ∗
    memRegion (fsp + 0x1758#64) (initLocalsSize - 0x1758)

theorem stage5ScratchAt_save_split_placed (fsp w5c0 w5c8 w5d0 : BitVec 64) :
    stage5ScratchAt fsp w5c0 w5c8 w5d0 =
      (((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        memRegion (fsp + 0x1600#64) 48) ∗
      stage5ScratchSaveRestPlaced fsp w5d0 := by
  dsimp only [stage5ScratchAt, stage5ScratchSaveRestPlaced]; ac_rfl

def stage5ScratchMemcpyRestPlaced (fsp w5c0 w5c8 w5d0 : BitVec 64) : SepProp :=
  memRegion (fsp + 0x5ba#64) 6 ∗
    ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
    ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
    ((fsp + 0x5d0#64) ↦₆₄ w5d0) ∗
    memRegion (fsp + 0x5d8#64) (0x1600 - 0x5d8) ∗
    memRegion (fsp + 0x1758#64) (initLocalsSize - 0x1758)

theorem stage5ScratchAt_memcpy_split_placed (fsp w5c0 w5c8 w5d0 : BitVec 64) :
    stage5ScratchAt fsp w5c0 w5c8 w5d0 =
      (memRegion (fsp + 0x1600#64) 48 ∗ memRegion (fsp + 0x1630#64) 296) ∗
      stage5ScratchMemcpyRestPlaced fsp w5c0 w5c8 w5d0 := by
  dsimp only [stage5ScratchAt, stage5ScratchMemcpyRestPlaced]; ac_rfl

/-- Minimal-frame segment `offSaveDeallocDone → offStore` (`+0x1734..+0x1764`):
clears `fsp + 0x5b9`, runs `memcpy(fsp + 0x1600, fsp + 0x460, 344)` and
`<SessionRecord>::promote_state(fsp + 0x128, fsp + 0x1600)` while preserving `A.pool lim st`. -/
theorem stage5_memcpy_promote_seg_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {B : RunBudgets} {ssBytes : List (BitVec 8)}
    {st : M.σ} {Rest : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hPromote : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hssLen : ssBytes.length = 344)
    (hpc : s.pc = initEntryPlaced + offSaveDeallocDone)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx26 : s.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64)
    (hnext : ∀ sm : State,
      sm.pc = initEntryPlaced + offStore →
      sm.status = .Running →
      sm.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs.files = s.fs.files →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
          ((fsp + 0x128#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
          ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
          ((fsp + 0x140#64) ↦ₛ ssBytes) ∗
          ((fsp + 0x1600#64) ↦ₛ ssBytes) ∗
          ((fsp + 0x460#64) ↦ₛ ssBytes) ∗
          ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
          A.pool lim st sm ∗
          stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      ((initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        ((fsp + 0x460#64) ↦ₛ ssBytes) ∗
        ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        memRegion (fsp + 0x1600#64) 344 ∗
        A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom := by
  intro fsp
  have hMemcpy := s5_memcpy_ok_at_placed hAlloc
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 20#5) = fsp + 0x460#64 at hx20
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep5 : ((fsp + 0x5b9#64) ↦₈ 1#8) ∗ ?remStep5 := by s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep5 (mid := lsρ memcpyName)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offSaveDeallocDone, lsρ] at hpc ⊢
    by_vm_steps (
      wp_steps
      simp (config := { failIfUnchanged := false }) only [hx26]
      try wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp5 hinv5; clear hpStep5
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_memcpy_pool_placed (A := A) (lim := lim) (s0 := s0)
    (ret_pc := initEntryPlaced + offAfterMemcpy)
    hMemcpy fsp (fsp + 0x1600#64) (fsp + 0x460#64) ssBytes st ?svF5
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offAfterMemcpy]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv5
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20])
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hssLen])
    ?svPre5 ?_
  case svPre5 =>
    rw [A.pool_of_vmPreserved hvmp5, hssLen]
    s5_close_frame
  intro sm5 hpc5 hrun5 hsp5 hal5 hcs5 hinv5 htr5 hfs5
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs5
  rcases hcs5 with ⟨hx19_5, _, _, _, _, _, _, _, _, _, _, hvregs_5⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  conv => arg 4; unfold initFreshRecAt; simp only [sepConj_assoc]
  s5_have_eq hpStep6 :
      (((fsp + 0x128#64) ↦₆₄ 0#64) ∗ ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
        ((fsp + 0x138#64) ↦₆₄ 0#64) ∗ ((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64)) ∗
      ?remStep6 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc5
  apply sepWPp_step_to_lscro_vm_mem_framed hinv5 hpStep6 (mid := lsmpl.base 47)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterMemcpy] at hpc5 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp6 hinv6; clear hpStep6
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (prom_le_stkSub hstk) (stkSub_hi hstk64),
        stackAt_96_eq_promoteState_cells fsp]
    simp only [sepConj_assoc]
  have haRec18 : (fsp + 0x128#64) + 0x18#64 = fsp + 0x140#64 := by bv_omega
  have haRec20 : (fsp + 0x128#64) + 0x20#64 = fsp + 0x148#64 := by bv_omega
  refine s5_call_promoteState_pool_placed (A := A) (lim := lim) (s0 := s0)
    (ret_pc := initEntryPlaced + offStore)
    hPromote fsp (fsp + 0x128#64) (fsp + 0x1600#64) ssBytes st ?svF6
    (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal5)
    (by dsimp only [initEntryPlaced, offStore]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr5]) hinv6
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5])
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5]) hssLen
    ?svPre6 ?_
  case svPre6 =>
    rw [A.pool_of_vmPreserved hvmp6, haRec18, haRec20]
    s5_close_frame
  intro sm6 hpc6 hrun6 hsp6 _hal6 hcs6 hinv6 htr6 hfs6
  have hfs6' : sm6.fs.files = s.fs.files := hfs6.trans hfs5
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_5, hsp5, hvregs_5] at hcs6
  rcases hcs6 with ⟨hx19_6, _, hx21_6, _, _, _, _, _, _, _, _, hvregs_6⟩
  conv => arg 4; rw [haRec18]
  s5_rw_pre (stackAt_96_eq_promoteState_cells fsp).symm
  s5_rw_pre (s5_stackAt_sub_split fsp (prom_le_stkSub hstk) (stkSub_hi hstk64)).symm
  refine sepWPp_weaken_pre ?_
    (hnext sm6 hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 hfs6' hx19_6 hx21_6)
  conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
  exact Entails.of_eq (by dsimp only [fsp]; s5_ac_rfl)

/-- Minimal-frame segment `offSave → offAfterSavePoll` (`+0x163c..+0x167c`):
writes `local_registration_id = reg` and `remote_registration_id = x.bundle.regId` into
`sessionStateAt`, then calls `idSaveShim` and `idSavePoll`. -/
theorem stage5_save_shim_poll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {x : InitGhost} {reg : BitVec 32}
    {sg₁ sg₂ : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {w5c8 : BitVec 64} {st : M.σ} {Rest : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hRodataSaveSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P))
    (hSaveShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hSavePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 565)
      (idSavePollSpecPlaced cliIo.rd cliWrOk A lim SaveEnv (stk - cliInitiateFrame)))
    (hFitShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hFitPoll : ∀ (fut : BitVec 64) (evsShim : List AllocEvent),
      BoxAllocEnv 32 evsShim →
      FitsEnv M lim (M.stepEvents evsShim st)
        (SaveEnv x.F
          { call :=
              { call :=
                  { addrA := x.peerA
                    addr := x.peer
                    keyA := x.bundleA + 0x78#64
                    key := x.bundle.idKey }
                fut := fut
                out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
            self := x.stores
            peers := StoresGhost.opened.identity.peers }))
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hsg₂ : sg₂ = { sg₁ with regIds := unpack32 x.bundle.regId ++ unpack32 reg })
    (hpc : s.pc = initEntryPlaced + offSave) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) (hsp_align : s0.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hfss : s.fs.files = x.F)
    (hx27 : (s.readReg64 (.gpr 27#5)).setWidth 32 = reg)
    (hnext : ∀ (sm : State) (fut : BitVec 64) (evsShim evsPoll : List AllocEvent)
      (gr : Except Unit (List (BitVec 8))) (pAns : Except Unit (Option IdentityKey))
      (JunkRO : SepProp),
      BoxAllocEnv 32 evsShim →
      SaveEnv x.F
        { call :=
            { call :=
                { addrA := x.peerA
                  addr := x.peer
                  keyA := x.bundleA + 0x78#64
                  key := x.bundle.idKey }
              fut := fut
              out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
          self := x.stores
          peers := StoresGhost.opened.identity.peers } evsPoll →
      gr = StoresGhost.opened.identity.peers.get cliIo.rd x.F x.peer.val.name →
      IdPeerAns gr pAns →
      sm.pc = initEntryPlaced + offAfterSavePoll →
      sm.status = .Running →
      sm.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs.files = x.F →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
          A.live fut 32 8 ∗
          idSaveBoxAt fut x.stores x.peerA (x.bundleA + 0x78#64) 1#8 ∗
          idSaveOutAt A.repAlloc (fsp + 0x1600#64) (idSaveOf pAns x.bundle.idKey) ∗
          dirAt A.repAlloc (x.stores + 0x28#64)
            (idSavePeers StoresGhost.opened.identity.peers x.peer.val.name x.bundle.idKey pAns) ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗
          FromRecordCallees.lsLogOff ∗
          sessionStateAt A.repAlloc (fsp + 0x460#64) sg₂ ss ∗
          ((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
          ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
          ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
          ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
          ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
          ((fsp + 0x5c0#64) ↦₆₄ fut) ∗
          ((fsp + 0x5c8#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
          A.pool lim (M.stepEvents evsPoll (M.stepEvents evsShim st)) sm ∗
          stackAt fsp (stk - cliInitiateFrame)) ∗ Rest ∗ JunkRO) Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      ((((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
        ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
        dirAt A.repAlloc (x.stores + 0x28#64) StoresGhost.opened.identity.peers ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗
        FromRecordCallees.lsLogOff ∗
        sessionStateAt A.repAlloc (fsp + 0x460#64) sg₁ ss ∗
        ((fsp + 0x5c0#64) ↦₆₄ (fsp + 0x460#64)) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        memRegion (fsp + 0x1600#64) 48 ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom := by
  intro fsp
  subst hsg₂
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpRegEq : sessionStateAt A.repAlloc (fsp + 0x460#64) sg₁ ss ∗ ?regRem := by
    s5_ac_rfl
  refine s5_apply_lens_oom hpRegEq fun R m hm => ?_
  obtain ⟨oldRem, oldLoc, SSRest, hmReg, hfoldRegIds⟩ :=
    sessionState_regIds_lens A.repAlloc (fsp + 0x460#64) sg₁ ss R m hm
  simp only [← sepConj_assoc] at hmReg
  refine ⟨_, hmReg, ?_⟩
  conv =>
    arg 4
    rw [show (fsp + 0x460#64) + 0x150#64 = fsp + 0x5b0#64 by bv_omega,
        show (fsp + 0x460#64) + 0x154#64 = fsp + 0x5b4#64 by bv_omega]
    simp only [sepConj_assoc]
  apply s5_with_rodata_oom (hRodataSaveSlot hinv.2)
  generalize hshim : lsmpl.base 600 = shimAddr
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep1 :
      (((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ shimAddr) ∗
        ((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
        ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
        ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64)) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗
        ((fsp + 0x5c0#64) ↦₆₄ (fsp + 0x460#64)) ∗
        ((fsp + 0x5b0#64) ↦₃₂ oldRem) ∗
        ((fsp + 0x5b4#64) ↦₃₂ oldLoc)) ∗ ?remStep1 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep1 (mid := shimAddr)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offSave] at hpc ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp1 hinv1; clear hpStep1; subst hshim
  have hregFold := hfoldRegIds x.bundle.regId reg
  let cSaveShim : IdentityShimCall :=
    { self := x.stores, addrA := x.peerA, keyA := x.bundleA + 0x78#64 }
  let cSave : IdentityCall :=
    { addrA := x.peerA, addr := x.peer, keyA := x.bundleA + 0x78#64, key := x.bundle.idKey }
  conv => arg 4; simp only [sepConj_assoc]
  refine s5_call_idSaveShim_placed (s0 := s0) (ret_pc := initEntryPlaced + offAfterSaveShim)
    hSaveShim fsp cSaveShim st ?svF1
    (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offAfterSaveShim]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv1
    (by dsimp only [cSaveShim]; wp_norm_goal)
    (by dsimp only [cSaveShim]; wp_norm_goal)
    (by dsimp only [cSaveShim]; wp_norm_goal)
    hFitShim ?svPre1 ?_
  case svPre1 =>
    rw [A.pool_of_vmPreserved hvmp1]
    s5_have_eq hpull :
        ((((fsp + 0x460#64) + 0x150#64) ↦₃₂ x.bundle.regId) ∗
          (((fsp + 0x460#64) + 0x154#64) ↦₃₂ reg) ∗ SSRest) ∗ ?restSv1 := by
      conv =>
        lhs
        simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp, hx27]
        rw [show fsp + 0x5b0#64 = (fsp + 0x460#64) + 0x150#64 by bv_omega,
            show fsp + 0x5b4#64 = (fsp + 0x460#64) + 0x154#64 by bv_omega]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull) (Entails.trans (sepConj_mono_left hregFold) ?_)
    s5_close_frame
  intro sm1 evsShim hboxShim hpc1 hrun1 hsp1 hal1 hcs1 hinv1 htr1 hfs1 hx1_1 hnz1 hal8_1
  have hx1_1_gpr : sm1.readReg64 (.gpr 1#5) = lsρ idSaveFutVtSym := hx1_1
  have hfs1' : sm1.fs.files = x.F := hfs1.trans hfss
  conv => arg 4; dsimp only [cSaveShim]; simp only [sepConj_assoc]
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  apply s5_with_rodata_oom (idSaveFut_poll_rodata_placed hinv1)
  generalize hpoll : lsmpl.base 565 = pollAddr
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep2 :
      (((lsρ idSaveFutVtSym + 24#64) ↦₆₄ᵣ pollAddr) ∗
        ((fsp + 0x5c0#64) ↦₆₄ (fsp + 0x460#64)) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8)) ∗ ?remStep2 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc1
  apply sepWPp_step_to_lscro_vm_mem_framed hinv1 hpStep2 (mid := pollAddr)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterSaveShim] at hpc1 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_1])
        (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro m2 hvmp2 hinv2; clear hpStep2; subst hpoll
  let gSave : IdPollGhost :=
    { call := { call := cSave, fut := sm1.readReg64 .x0, out := fsp + 0x1600#64 },
      self := x.stores, peers := StoresGhost.opened.identity.peers }
  have hfs1_m2 : (sm1.setMem m2).fs.files = x.F := hfs1'
  have hwfPeers :
      ∀ bs, gSave.peers.get cliIo.rd (sm1.setMem m2).fs.files x.peer.val.name = .ok bs →
        IdFileWf bs := by
    dsimp only [gSave, cSave]; rw [hfs1_m2]
    obtain ⟨bs₀, hbs₀, hwf₀⟩ := hinitOk.idGet
    intro bs hbs; rw [hbs₀] at hbs; injection hbs with hEq; exact hEq ▸ hwf₀
  conv => arg 4; simp only [sepConj_assoc]
  refine s5_call_idSavePoll_placed (s0 := s0) (ret_pc := initEntryPlaced + offAfterSavePoll)
    hSavePoll fsp gSave (M.stepEvents evsShim st) ?svF2
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_1]) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal1)
    (by dsimp only [initEntryPlaced, offAfterSavePoll]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr1]) hinv2
    (by dsimp only [gSave, cSave]; wp_norm_goal)
    (by dsimp only [gSave, cSave]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    hinitOk.nameLt opened_peers_bounds.1 opened_peers_bounds.2
    ⟨by dsimp only [gSave, cSave]; exact hinitOk.idPathOk,
     by dsimp only [gSave, cSave]; exact hinitOk.idPathLt⟩ hwfPeers
    (by change FitsEnv M lim (M.stepEvents evsShim st) (SaveEnv sm1.fs.files gSave)
        rw [hfs1']
        exact hFitPoll (sm1.readReg64 .x0) evsShim hboxShim)
    ?svPre2 ?_
  case svPre2 =>
    rw [A.pool_of_vmPreserved hvmp2]
    dsimp only [gSave, cSave]; s5_close_frame
  intro sm2 evsPoll gr pAns hstPoll hpc2 hrun2 hsp2 hal2 hcs2 hinv2 htr2 hfs2 hgr hpAns
  conv => arg 4; dsimp only [gSave, cSave]
  have hstPoll' : SaveEnv x.F gSave evsPoll := by rwa [← hfs1_m2]
  have hfs2' : sm2.fs.files = x.F := hfs2.trans hfs1_m2
  have hgr' : gr = StoresGhost.opened.identity.peers.get cliIo.rd x.F x.peer.val.name := by
    dsimp only [gSave, cSave] at hgr
    simpa (config := { zetaDelta := false }) only [wp_norm, arm64_norm, hfs1'] using hgr
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_1, hx20_1, hx1_1, hsp1, hvregs_1] at hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  refine sepWPp_weaken_pre ?_
    (hnext sm2 (sm1.readReg64 .x0) evsShim evsPoll gr pAns ?junkRO1 hboxShim hstPoll'
      hgr' hpAns hpc2 hrun2 hsp2 hvregs_2 hinv2 htr2 hfs2' hx19_2 hx20_2)
  conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp, hsp1, hx1_1_gpr]
  exact Entails.of_eq (by dsimp only [Reg.x0, fsp]; s5_ac_rfl)

/-- Minimal-frame segment `offAfterSavePoll → offSaveDeallocDone` (`+0x1680..+0x1730`):
unpacks `idSaveOutAt` (`Ok(cg)`), runs `futDrop` and `__rust_dealloc(fut, 32, 8)`, and collapses
the 48-byte sret scratch slot. -/
theorem stage5_save_drop_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {B : RunBudgets} {x : InitGhost} {fut : BitVec 64} {cg : IdentityChange}
    {st : M.σ} {Rest : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hpc : s.pc = initEntryPlaced + offAfterSavePoll)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) (hsp_align : s0.spAligned = true)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hnext : ∀ (sm : State) (JunkRO : SepProp),
      sm.pc = initEntryPlaced + offSaveDeallocDone →
      sm.status = .Running →
      sm.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs.files = s.fs.files →
      sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
          ((fsp + 0x5c0#64) ↦₆₄ fut) ∗
          ((fsp + 0x5c8#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
          memRegion (fsp + 0x1600#64) 48 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 32 8) st) sm ∗
          stackAt fsp (stk - cliInitiateFrame)) ∗ Rest ∗ JunkRO) Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      ((A.live fut 32 8 ∗
        idSaveBoxAt fut x.stores x.peerA (x.bundleA + 0x78#64) 1#8 ∗
        idSaveOutAt A.repAlloc (fsp + 0x1600#64) (.ok cg) ∗
        ((fsp + 0x5c0#64) ↦₆₄ fut) ∗
        ((fsp + 0x5c8#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom := by
  intro fsp
  have hDealloc := s5_dealloc_ok_at_placed hAlloc
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  have houtUnpack :
      idSaveOutAt A.repAlloc (fsp + 0x1600#64) (.ok cg) ⊢
        ∃∗ sw1 : BitVec 64, ∃∗ sw2 : BitVec 64, ∃∗ sw3 : BitVec 64,
        ∃∗ sw4 : BitVec 64, ∃∗ sw5 : BitVec 64,
          ⌜sw1.setWidth 32 = (if cg == .replacedExisting then 1#32 else 0#32)⌝ ∗
          ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ sw1) ∗ (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ sw2) ∗
          (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ sw3) ∗ (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ sw4) ∗
          (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ sw5) := by
    dsimp only [idSaveOutAt]
    refine Entails.trans
      (sepConj_mono_right (u32_tail36_words5 (fsp + 0x1600#64)
        (if cg == .replacedExisting then 1#32 else 0#32))) ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun sw1 => Entails.sepExists_elim fun sw2 =>
      Entails.sepExists_elim fun sw3 => Entails.sepExists_elim fun sw4 =>
      Entails.sepExists_elim fun sw5 => ?_
    exact Entails.sepExists_right sw1 (Entails.sepExists_right sw2
      (Entails.sepExists_right sw3 (Entails.sepExists_right sw4
        (Entails.sepExists_right sw5 (Entails.of_eq (by ac_rfl))))))
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpOutEq : idSaveOutAt A.repAlloc (fsp + 0x1600#64) (.ok cg) ∗ ?outRem := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq hpOutEq) (sepConj_mono_left houtUnpack)) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro sw1; apply sepWPp_exists_left; intro sw2
  apply sepWPp_exists_left; intro sw3; apply sepWPp_exists_left; intro sw4
  apply sepWPp_exists_left; intro sw5; apply sepWPp_pure_left; intro _
  have hsretOffs := sret_word_offs fsp
  conv => arg 4; rw [hsretOffs.1, hsretOffs.2.1, hsretOffs.2.2.1, hsretOffs.2.2.2.1, hsretOffs.2.2.2.2]
  apply s5_with_rodata_oom (idSaveFut_drop_rodata_placed hinv)
  generalize hdrop : lsmpl.base 547 = dropAddr
  s5_have_eq hpStep3 :
      (((lsρ idSaveFutVtSym) ↦₆₄ᵣ dropAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((fsp + 5640#64) ↦₆₄ sw1) ∗ ((fsp + 5648#64) ↦₆₄ sw2) ∗ ((fsp + 5656#64) ↦₆₄ sw3) ∗
        ((fsp + 5664#64) ↦₆₄ sw4) ∗ ((fsp + 5672#64) ↦₆₄ sw5) ∗
        ((fsp + 1480#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
        ((fsp + 1472#64) ↦₆₄ fut)) ∗
      (A.live fut 32 8 ∗
        idSaveBoxAt fut x.stores x.peerA (x.bundleA + 0x78#64) 1#8 ∗
        A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Rest) := by
    s5_ac_rfl
  suffices hAfterDrop : ∀ (sm3 : State) (dAddr : BitVec 64) {P3 : SepProp},
      P3 = (((lsρ idSaveFutVtSym) ↦₆₄ᵣ dAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((fsp + 5640#64) ↦₆₄ sw1) ∗ ((fsp + 5648#64) ↦₆₄ sw2) ∗ ((fsp + 5656#64) ↦₆₄ sw3) ∗
        ((fsp + 5664#64) ↦₆₄ sw4) ∗ ((fsp + 5672#64) ↦₆₄ sw5) ∗
        ((fsp + 1480#64) ↦₆₄ lsρ idSaveFutVtSym) ∗
        ((fsp + 1472#64) ↦₆₄ fut)) ∗
      (A.live fut 32 8 ∗
        idSaveBoxAt fut x.stores x.peerA (x.bundleA + 0x78#64) 1#8 ∗
        A.pool lim st sm3 ∗ stackAt fsp (stk - cliInitiateFrame) ∗ Rest) →
      sm3.pc = initEntryPlaced + offSaveDealloc →
      sm3.status = .Running →
      sm3.sp = fsp →
      sm3.spAligned = true →
      sm3.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm3.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm3.readReg64 (.gpr 22#5) = lsρ idSaveFutVtSym →
      sm3.readReg64 (.gpr 23#5) = fut →
      sm3.readReg64 (.gpr 26#5) = 0xFFFFFFFFFFFFFFFE#64 →
      calleeSavedVRegs sm3 = calleeSavedVRegs s →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm3.mem →
      sm3.trace = s0.trace →
      sm3.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm3 P3 Q Qp oom by
    rw [initEntryPlaced_eq_blkPl] at hpc
    by_cases hdropNe : dropAddr = 0#64
    · apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep3 (mid := initEntryPlaced + offSaveDealloc)
      · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterSavePoll, offSaveDealloc] at hpc ⊢
        rw [initEntryPlaced_eq_blkPl]
        by_vm_steps (
          wp_steps
          simp (config := { failIfUnchanged := false }) only [
            hdropNe, beq_self_eq_true, ↓reduceIte]
          try wp_steps
          apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
            (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
          exact ⟨state_exists_setMem _, rfl⟩)
      intro _ hvmp3 hinv3; clear hpStep3
      refine sepWPp_weaken_pre (by rw [← A.pool_of_vmPreserved hvmp3]; exact Entails.refl _) ?_
      exact hAfterDrop _ 0#64 rfl
        (by dsimp only [initEntryPlaced, offSaveDealloc]; wp_norm_goal; try rfl)
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
        (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using halign_s)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [calleeSavedVRegs, wp_norm, arm64_norm])
        hinv3
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr])
        (by wp_norm_goal)
    · apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep3 (mid := dropAddr)
      · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterSavePoll] at hpc ⊢
        by_vm_steps (
          wp_steps
          simp (config := { failIfUnchanged := false }) only [
            beq_eq_false_iff_ne.mpr hdropNe, Bool.false_eq_true, ↓reduceIte]
          try wp_steps
          apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
            (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
          exact ⟨state_exists_setMem _, rfl⟩)
      intro _ hvmp3 hinv3; clear hpStep3; subst hdrop
      refine s5_call_futDrop_pool_placed (A := A) (lim := lim) (s0 := s0)
        (ret_pc := initEntryPlaced + offSaveDealloc)
        hFutDrop fsp st ?stF3
        (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
        (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
        (by dsimp only [initEntryPlaced, offSaveDealloc]; wp_norm_goal; try rfl)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv3
        ?stPre3 ?_
      case stPre3 =>
        rw [A.pool_of_vmPreserved hvmp3]
        s5_close_frame
      intro sm3 hpc3 hrun3 hsp3 hal3 hcs3 hinv3 htr3 hfs3
      simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs3
      rcases hcs3 with ⟨hx19_3, hx20_3, _, hx22_3, hx23_3, _, _, hx26_3, _, _, _, hvregs_3⟩
      refine sepWPp_weaken_pre (Entails.of_eq (by s5_ac_rfl))
        (hAfterDrop sm3 (lsmpl.base 547) rfl hpc3 hrun3 hsp3 hal3 hx19_3 hx20_3 hx22_3 hx23_3
          hx26_3 hvregs_3 hinv3 htr3 hfs3)
  clear hpStep3
  intro sm3 dAddr P3 hP3Eq hpc3 hrun3 hsp3 hal3 hx19_3 hx20_3 hx22_3 hx23_3 hx26_3 hvregs_3 hinv3 htr3 hfs3
  subst hP3Eq
  apply s5_with_rodata_oom (idSaveFut_size_rodata_placed hinv3)
  apply s5_with_rodata_oom (idSaveFut_align_rodata_placed hinv3)
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep4 :
      (((lsρ idSaveFutVtSym + 8#64) ↦₆₄ᵣ 32#64) ∗
        ((lsρ idSaveFutVtSym + 16#64) ↦₆₄ᵣ 8#64)) ∗ ?remStep4 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc3
  apply sepWPp_step_to_lscro_vm_mem_framed hinv3 hpStep4 (mid := lsρ lsRustDeallocSymCli)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offSaveDealloc, lsρ] at hpc3 hx22_3 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp4 hinv4; clear hpStep4
  have hboxMem := idSaveBoxAt_entails_memRegion32 fut x.stores x.peerA (x.bundleA + 0x78#64) 1#8
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dealloc_placed (s0 := s0) (ret_pc := initEntryPlaced + offSaveDeallocDone)
    hDealloc fsp fut 32 8 st ?stF4
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal3)
    (by dsimp only [initEntryPlaced, offSaveDeallocDone]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]) hinv4
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_3])
    (by wp_norm_goal) (by wp_norm_goal) ⟨layoutOk_32_8, by decide⟩
    ?stPre4 ?_
  case stPre4 =>
    rw [A.pool_of_vmPreserved hvmp4]
    s5_have_eq hpull :
        idSaveBoxAt fut x.stores x.peerA (x.bundleA + 0x78#64) 1#8 ∗ ?restSvBox := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp3]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hboxMem) ?_)
    s5_close_frame
  intro sm4 hpc4 hrun4 hsp4 _hal4 hcs4 hinv4 htr4 hfs4
  have hfs4' : sm4.fs.files = s.fs.files := hfs4.trans hfs3
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_3, hx20_3, hx26_3, hvregs_3] at hcs4
  rcases hcs4 with ⟨hx19_4, hx20_4, _, _, _, _, _, hx26_4, _, _, _, hvregs_4⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  have hw48 := words6_entails_memRegion48 (fsp + 0x1600#64)
    0xFFFFFFFFFFFFFFFE#64 sw1 sw2 sw3 sw4 sw5
  refine sepWPp_weaken_pre ?_
    (hnext sm4 ?junkRO2 hpc4 hrun4 hsp4 hvregs_4 hinv4 htr4 hfs4' hx19_4 hx20_4 hx26_4)
  have hsretSymm := sret_word_offs_symm fsp
  s5_have_eq hp1 :
      (((fsp + 0x1600#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ sw1) ∗ (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ sw2) ∗
        (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ sw3) ∗ (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ sw4) ∗
        (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ sw5)) ∗ ?remW48 := by
    conv =>
      lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp, hsp3]
      rw [hsretSymm.1, hsretSymm.2.1, hsretSymm.2.2.1, hsretSymm.2.2.2.1, hsretSymm.2.2.2.2]
    s5_ac_rfl
  refine Entails.trans (Entails.of_eq hp1) (Entails.trans (sepConj_mono_left hw48) ?_)
  exact Entails.of_eq (by dsimp only [fsp]; s5_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudgetAux

end
