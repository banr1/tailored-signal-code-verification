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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Stage 5 `get_local_registration_id` Shim, Poll, and Branch (`[LibsignalPlacement]`)

Verifies `stage5_reg_shim_poll_placed_ok` (`+0x14b8..+0x14e0`) and
`stage5_reg_and_branch_placed_ok` (`+0x14b8 → lr`) on `initProgPlaced W` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr hiding utf8
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
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  setUnackPreKeyMsgEpochInnerSpec idOwnShimSpecPlaced idRegIdPollSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (sepWPp_weaken_pre sepWPp_pure_left sepWPp_exists_left)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas hiding
  s5_call_raw_placed s5_dealloc_ok_at_placed s5_memcpy_ok_at_placed s5_call_futDrop_placed
  s5_call_dealloc_placed s5_call_dropSS_placed s5_call_setUnackMsg_placed
  s5_call_setUnackKyb_placed s5_call_idRegIdShim_placed s5_call_idRegIdPoll_placed
  s5_call_idSaveShim_placed s5_call_idSavePoll_placed s5_call_memcpy_placed
  s5_call_promoteState_placed s5_call_sessStoreShim_placed s5_call_sessStorePoll_placed
  stage5_epilogue_placed_ok stage5_err_cleanup_placed_ok stage5_cleanup_after_store_placed_ok
  stage5_store_and_cleanup_placed_ok stage5_accept_placed_ok stage5_reg_drop_dealloc_placed_ok
  stage5_branch_after_reg_placed_ok stage5_reg_and_branch_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced idOwnShimSpecPlaced idRegIdPollSpecPlaced
   idSaveShimSpecPlaced idSavePollSpecPlaced sessStoreShimSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec s5_call_idRegIdShim_placed s5_call_idRegIdPoll_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
  (sepWPp_step_to_lscro_vm_mem_framed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget
  (initIdSavePollGhost initSessStorePollGhost
   stage5_reg_drop_dealloc_placed_ok stage5_branch_after_reg_placed_ok)
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

/-- Ghost argument passed to `idRegIdPollSpecPlaced` during Stage 5 `get_local_registration_id`. -/
abbrev initIdRegIdPollGhostPlaced (x : InitGhost) (s0 : State) (futReg : BitVec 64) :
    IdOwnPollGhostPlaced :=
  { fut := futReg
    out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64
    self := x.stores
    own := StoresGhost.opened.identity.own }

/-! ## Minimal-Frame Decomposition -/

def initArgsRegRestPlaced [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) : SepProp :=
  ((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
    ((fsp + 0xd8#64) ↦₆₄ x.meA) ∗
    ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
    ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym) ∗
    ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
    ((fsp + 0x108#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (fsp + 0x114#64) 4 ∗
    ((fsp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
    ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64))

theorem initArgsAtPlaced_reg_split [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost)
    (s0 : State) :
    initArgsAtPlaced fsp x s0 =
      (((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym)) ∗
      initArgsRegRestPlaced fsp x s0 := by
  dsimp only [initArgsAtPlaced, initArgsRegRestPlaced]; s5_ac_rfl

def storesRegRest (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : SepProp :=
  dirAt A (a + 0x28#64) g.identity.peers ∗
    dirAt A (a + 0x50#64) g.signed ∗
    dirAt A (a + 0x78#64) g.kyber.oneTime ∗
    dirAt A (a + 0xa0#64) g.kyber.lastResort ∗
    dirAt A (a + 0xc8#64) g.oneTime ∗
    dirAt A (a + 0xf0#64) g.sessions ∗
    dirAt A (a + 0x118#64) g.pub

theorem storesAt_reg_split (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) :
    storesAt A a g = dirAt A a g.identity.own ∗ storesRegRest A a g := by
  rfl

def stage5ScratchRegRest (fsp : BitVec 64) : SepProp :=
  memRegion (fsp + 0x5ba#64) 6 ∗
    memRegion (fsp + 0x5d8#64) (0x1600 - 0x5d8) ∗
    memRegion (fsp + 0x1630#64) 296 ∗
    memRegion (fsp + 0x1758#64) (initLocalsSize - 0x1758)

theorem stage5ScratchAt_reg_split (fsp w5c0 w5c8 w5d0 : BitVec 64) :
    stage5ScratchAt fsp w5c0 w5c8 w5d0 =
      (((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        ((fsp + 0x5d0#64) ↦₆₄ w5d0) ∗
        memRegion (fsp + 0x1600#64) 48) ∗
      stage5ScratchRegRest fsp := by
  dsimp only [stage5ScratchAt, stage5ScratchRegRest]; s5_ac_rfl

/-- Minimal-frame segment `offAfterUnackKyb → offAfterRegPoll` (`+0x14b8 .. +0x14e0`):
runs `idRegIdShim` (`lsmpl.base 603`) and `idRegIdPoll` (`lsmpl.base 568`) while storing
`fsp + 0x460#64`, `futReg`, and `lsρ idRegIdFutVtSym` at `fsp + 0x5c0..0x5d0`. -/
theorem stage5_reg_shim_poll_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {RegPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W] {x : InitGhost} {st : M.σ}
    {w5c0 w5c8 w5d0 : BitVec 64} {Rest : SepProp} {stk : Nat}
    {s0 s : State} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hRodataRegIdSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliIdentityVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P))
    (hRegShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim (stk - cliInitiateFrame)))
    (hRegPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 568)
      (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim RegPollEnv (stk - cliInitiateFrame)))
    (hFitShim : FitsEnv M lim st (BoxAllocEnv 16))
    (hFitPoll : ∀ (futReg : BitVec 64) (evsShim : List AllocEvent),
      BoxAllocEnv 16 evsShim →
      FitsEnv M lim (M.stepEvents evsShim st)
        (RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg)))
    (hpc : s.pc = initEntryPlaced + offAfterUnackKyb)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hsp_align : s0.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hnext : ∀ (sm : State) (futReg : BitVec 64) (evsShim evsPoll : List AllocEvent)
        (ans : Except Unit (BitVec 32)) (JunkRO : SepProp),
      BoxAllocEnv 16 evsShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsPoll →
      ans = StoresGhost.opened.identity.regId cliIo.rd x.F →
      sm.pc = initEntryPlaced + offAfterRegPoll →
      sm.status = .Running →
      sm.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame →
      sm.spAligned = true →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      sm.fs.files = x.F →
      sm.readReg64 (.gpr 19#5) = x.ret →
      sm.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm
        ((let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
          idRegIdOutAt A.repAlloc (fsp + 0x1600#64) ans ∗
          idOwnFutBoxAt futReg x.stores 1#8 ∗
          A.live futReg 16 8 ∗
          dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
          ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
          ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
          ((fsp + 0x5c0#64) ↦₆₄ (fsp + 0x460#64)) ∗
          ((fsp + 0x5c8#64) ↦₆₄ futReg) ∗
          ((fsp + 0x5d0#64) ↦₆₄ lsρ idRegIdFutVtSym) ∗
          A.pool lim (M.stepEvents evsPoll (M.stepEvents evsShim st)) sm ∗
          stackAt fsp (stk - cliInitiateFrame)) ∗ Rest ∗ JunkRO) Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      ((((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        ((fsp + 0x5d0#64) ↦₆₄ w5d0) ∗
        memRegion (fsp + 0x1600#64) 48 ∗
        A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) Q Qp oom := by
  intro fsp
  have halign_s : s.spAligned = true := spAligned_fsp hsp_align hsp
  change s.sp = fsp at hsp
  change s.readReg64 (.gpr 20#5) = fsp + 0x460#64 at hx20
  apply s5_with_rodata_oom (hRodataRegIdSlot hinv.2)
  generalize hshim : lsmpl.base 603 = shimAddr
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep3 :
      (((lsρ cliIdentityVtSym + 32#64) ↦₆₄ᵣ shimAddr) ∗
        ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        ((fsp + 0x5d0#64) ↦₆₄ w5d0)) ∗ ?remStep3 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc
  apply sepWPp_step_to_lscro_vm_mem_framed hinv hpStep3 (mid := shimAddr)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterUnackKyb] at hpc ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp3 hinv3; clear hpStep3; subst hshim
  conv => arg 4; simp only [sepConj_assoc]
  refine s5_call_idRegIdShim_placed (s0 := s0) (ret_pc := initEntryPlaced + offAfterRegShim)
    hRegShim fsp x.stores st ?eF3
    (by wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s)
    (by dsimp only [initEntryPlaced, offAfterRegShim]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv3
    (by wp_norm_goal) hFitShim ?ePre3 ?_
  case ePre3 =>
    rw [A.pool_of_vmPreserved hvmp3]
    s5_close_frame
  intro sm3 evsShim hboxShim hpc3 hrun3 hsp3 hal3 hcs3 hinv3 htr3 hfs3 hx1_3 _hnz3 _hal8_3
  have hx1_3_gpr : sm3.readReg64 (.gpr 1#5) = lsρ idRegIdFutVtSym := hx1_3
  have hfs3' : sm3.fs.files = x.F := hfs3.trans hfss
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19, hx20, hvregs] at hcs3
  rcases hcs3 with ⟨hx19_3, hx20_3, _, _, _, _, _, _, _, _, _, hvregs_3⟩
  apply s5_with_rodata_oom (idRegIdFut_poll_rodata_placed hinv3)
  generalize hpoll : lsmpl.base 568 = pollAddr
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep4Swap :
      ((A.live (sm3.readReg64 .x0) 16 8 ∗
        idOwnFutBoxAt (sm3.readReg64 .x0) x.stores 0#8 ∗
        dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        memRegion (fsp + 0x1600#64) 48 ∗
        A.pool lim (M.stepEvents evsShim st) sm3 ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ Rest) ∗ ?p0Step4 := by
    s5_ac_rfl
  have hpStep4 : _ = ?p0Step4 ∗ _ := hpStep4Swap.trans (sepConj_comm _ _)
  rw [initEntryPlaced_eq_blkPl] at hpc3
  apply sepWPp_step_to_lscro_vm_mem_framed hinv3 hpStep4 (mid := pollAddr)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterRegShim] at hpc3 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_3])
        (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro m4 hvmp4 hinv4; clear hpStep4 hpStep4Swap; subst hpoll
  let gReg : IdOwnPollGhost :=
    { fut := sm3.readReg64 .x0
      out := fsp + 0x1600#64
      self := x.stores
      own := StoresGhost.opened.identity.own }
  have hfs3_m4 : (sm3.setMem m4).fs.files = x.F := hfs3'
  conv => arg 4; simp only [sepConj_assoc]
  refine s5_call_idRegIdPoll_placed (s0 := s0) (ret_pc := initEntryPlaced + offAfterRegPoll)
    hRegPoll fsp gReg (M.stepEvents evsShim st) ?eF4
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx1_3])
    (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal3)
    (by dsimp only [initEntryPlaced, offAfterRegPoll]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr3]) hinv4
    (by dsimp only [gReg]; wp_norm_goal)
    (by dsimp only [gReg]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp3])
    opened_own_regId_pre.1 opened_own_regId_pre.2
    (by change FitsEnv M lim (M.stepEvents evsShim st)
          (RegPollEnv (sm3.setMem m4).fs.files (initIdRegIdPollGhostPlaced x s0 (sm3.readReg64 .x0)))
        rw [hfs3_m4]
        exact hFitPoll (sm3.readReg64 .x0) evsShim hboxShim)
    ?ePre4 ?_
  case ePre4 =>
    rw [A.pool_of_vmPreserved hvmp4]
    dsimp only [gReg]; s5_close_frame
  intro sm4 evsPoll ans hstPoll hpc4 hrun4 hsp4 hal4 hcs4 hinv4 htr4 hfs4 hansReg
  conv => arg 4; dsimp only [gReg]; simp only [sepConj_assoc]
  have hstPoll' : RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 (sm3.readReg64 .x0)) evsPoll := by
    rwa [← hfs3_m4]
  have hfs4' : sm4.fs.files = x.F := hfs4.trans hfs3_m4
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_3, hx20_3, hvregs_3] at hcs4
  rcases hcs4 with ⟨hx19_4, hx20_4, _, _, _, _, _, _, _, _, _, hvregs_4⟩
  have hansReg' : ans = StoresGhost.opened.identity.regId cliIo.rd x.F := by
    dsimp only [gReg, IdGhost.regId] at hansReg ⊢
    simpa (config := { zetaDelta := false }) only [wp_norm, arm64_norm, hfs3'] using hansReg
  refine sepWPp_weaken_pre ?_
    (hnext sm4 (sm3.readReg64 .x0) evsShim evsPoll ans ?junkRO1 hboxShim hstPoll' hansReg'
      hpc4 hrun4 hsp4 hal4 hvregs_4 hinv4 htr4 hfs4' hx19_4 hx20_4)
  conv =>
    lhs
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [
      BitVec.add_zero, hsp, hsp3, hx20, hx20_3, hx1_3, hx1_3_gpr,
      show fsp + 1472#64 = fsp + 0x5c0#64 by bv_omega,
      show fsp + 1480#64 = fsp + 0x5c8#64 by bv_omega,
      show fsp + 1488#64 = fsp + 0x5d0#64 by bv_omega]
  exact Entails.of_eq (by dsimp only [Reg.x0, fsp]; s5_ac_rfl)

/-- Budget-threaded continuation from `offAfterUnackKyb` (`+0x14b8`) on `initProgPlaced W`:
calls `get_local_registration_id` shim + poll + future drop + box dealloc, then branches on `ans`
to `EpiloguePlacedBudget.stage5_err_cleanup_placed_ok` (`.error ()`) or
`AcceptTailPlacedBudget.stage5_accept_placed_ok` (`.ok reg`). -/
theorem stage5_reg_and_branch_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {RegPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr dataPtr w5c0 w5c8 w5d0 : BitVec 64} {opkId padVal w1_kyb : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {BRest Extra : SepProp} {stk : Nat} {s0 s5 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRodataRegIdSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliIdentityVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 603) ∗ P))
    (hRegShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim (stk - cliInitiateFrame)))
    (hRegPoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 568)
      (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim RegPollEnv (stk - cliInitiateFrame)))
    (hRodataSaveSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliIdentityVtSym + 40#64) ↦₆₄ᵣ lsmpl.base 600) ∗ P))
    (hSaveShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hSavePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 565)
      (idSavePollSpecPlaced cliIo.rd cliWrOk A lim SaveEnv (stk - cliInitiateFrame)))
    (hPromote : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec))
    (hRodataStoreSlot : ∀ {m : Memory} {P : SepProp},
      LibsignalRoLoaded lsmpl m → (m ⊨ P) →
        (m ⊨ ((lsρ cliSessionVtSym + 32#64) ↦₆₄ᵣ lsmpl.base 605) ∗ P))
    (hStoreShim : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (hStorePoll : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim StoreEnv (stk - cliInitiateFrame)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hDropSS : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (hFitRegShim : FitsEnv M lim st (BoxAllocEnv 16))
    (hFitRegPoll : ∀ (futReg : BitVec 64) (evsRegShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      FitsEnv M lim (M.stepEvents evsRegShim st)
        (RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg)))
    (hEnvErr : StoresGhost.opened.identity.regId cliIo.rd x.F = .error () →
      ∀ (futReg : BitVec 64) (evsRegShim evsRegPoll evsDrop : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1)
          (M.stepEvents evsDrop
            (M.stepEvents (rustDeallocEvents 16 8)
              (M.stepEvents evsRegPoll (M.stepEvents evsRegShim st)))) =
          M.stepEvents evs st0)
    (hFitSaveShim : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg : BitVec 64) (evsRegShim evsRegPoll : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      FitsEnv M lim
        (M.stepEvents (rustDeallocEvents 16 8)
          (M.stepEvents evsRegPoll (M.stepEvents evsRegShim st)))
        (BoxAllocEnv 32))
    (hFitSavePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave : BitVec 64) (evsRegShim evsRegPoll evsSaveShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      FitsEnv M lim
        (M.stepEvents evsSaveShim
          (M.stepEvents (rustDeallocEvents 16 8)
            (M.stepEvents evsRegPoll (M.stepEvents evsRegShim st))))
        (SaveEnv x.F (initIdSavePollGhost x s0 futSave)))
    (hFitStoreShim : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave : BitVec 64)
        (evsRegShim evsRegPoll evsSaveShim evsSavePoll : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
      FitsEnv M lim
        (M.stepEvents (rustDeallocEvents 32 8)
          (M.stepEvents evsSavePoll
            (M.stepEvents evsSaveShim
              (M.stepEvents (rustDeallocEvents 16 8)
                (M.stepEvents evsRegPoll (M.stepEvents evsRegShim st))))))
        (BoxAllocEnv 32))
    (hFitStorePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave futStore : BitVec 64)
        (evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
      BoxAllocEnv 32 evsStoreShim →
      FitsEnv M lim
        (M.stepEvents evsStoreShim
          (M.stepEvents (rustDeallocEvents 32 8)
            (M.stepEvents evsSavePoll
              (M.stepEvents evsSaveShim
                (M.stepEvents (rustDeallocEvents 16 8)
                  (M.stepEvents evsRegPoll (M.stepEvents evsRegShim st)))))))
        (StoreEnv
          (initSessStorePollGhost x be kp hdr dataPtr opkId reg padVal w1_kyb sg ss kg s0 futStore)))
    (hEnvOk : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave futStore : BitVec 64)
        (evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop :
          List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
      BoxAllocEnv 32 evsStoreShim →
      StoreEnv
        (initSessStorePollGhost x be kp hdr dataPtr opkId reg padVal w1_kyb sg ss kg s0 futStore)
        evsStorePoll →
      FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents evsDrop
          (M.stepEvents (rustDeallocEvents 1568 1)
            (M.stepEvents (rustDeallocEvents 32 8)
              (M.stepEvents evsStorePoll
                (M.stepEvents evsStoreShim
                  (M.stepEvents (rustDeallocEvents 32 8)
                    (M.stepEvents evsSavePoll
                      (M.stepEvents evsSaveShim
                        (M.stepEvents (rustDeallocEvents 16 8)
                          (M.stepEvents evsRegPoll (M.stepEvents evsRegShim st)))))))))) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩) (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (halice : sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
    (hkgBytes : kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt)
    (hkemLen : (0x08#8 :: ofU8 hdr.kemCt).length = 1569)
    (hkyberKey : kyberKey (u8Vec 1568 hdr.kemCt) = 0x08#8 :: ofU8 hdr.kemCt)
    (hekLen : ekASk.length = 32 ∧ ekAPk.length = 32) (hkpkLen : x.bundle.kpk.length = 1568)
    (hfoldBundle :
      ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ⊢
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr)
    (hpc : s.pc = initEntryPlaced + offAfterUnackKyb)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hfs0 : s0.fs.files = x.F) (hfss : s.fs.files = x.F)
    (hx19 : s.readReg64 (.gpr 19#5) = x.ret)
    (hx20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₁ : SessionGhost := { sg with pending := some pg, kyber := some kg' }
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗
        A.pool lim st s ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗ initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A.repAlloc (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        stage5ScratchAt fsp w5c0 w5c8 w5d0 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp oom := by
  intro fsp opkFlag pg kg' sg₁
  conv =>
    arg 4
    rw [storesAt_reg_split, initArgsAtPlaced_reg_split, stage5ScratchAt_reg_split]
    simp only [sepConj_assoc]
  s5_have_eq hpPreReg :
      (((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
        ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
        dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
        ((fsp + 0x5c0#64) ↦₆₄ w5c0) ∗
        ((fsp + 0x5c8#64) ↦₆₄ w5c8) ∗
        ((fsp + 0x5d0#64) ↦₆₄ w5d0) ∗
        memRegion (fsp + 0x1600#64) 48 ∗
        A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame)) ∗ ?remReg := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.of_eq hpPreReg)
    (stage5_reg_shim_poll_placed_ok hRodataRegIdSlot hRegShim hRegPoll hFitRegShim hFitRegPoll
      hpc hrun hsp hs5.ctrl.spAligned hvregs hinv htr hfss hx19 hx20 ?_)
  intro sm4 futReg evsRegShim evsRegPoll ans JunkRO1 hboxRegShim hstRegPoll hansReg'
    hpc4 hrun4 hsp4 hal4 hvregs_4 hinv4 htr4 hfs4' hx19_4 hx20_4
  conv => arg 4; dsimp only; simp only [sepConj_assoc]
  s5_have_eq hpRegOut : idRegIdOutAt A.repAlloc (fsp + 0x1600#64) ans ∗ ?regOutRem := by
    dsimp only [fsp] at *; s5_ac_rfl
  refine s5_apply_lens_oom hpRegOut fun R3 m3 hm3 => ?_
  obtain ⟨rw0, rw1, rw2, rw3, rw4, rw5, SpeH, hrw0_ne3, hmAns, hansBranch⟩ :=
    unpack_idRegIdOutAt A.repAlloc fsp x.ret ans R3 m3 hm3
  simp only [← sepConj_assoc] at hmAns
  refine ⟨_, hmAns, ?_⟩
  refine sepWPp_weaken_pre ?pre1
    (stage5_reg_drop_dealloc_placed_ok (B := B)
      (st := M.stepEvents evsRegPoll (M.stepEvents evsRegShim st))
      (fsp := fsp) (storesPtr := x.stores) (futPtr := futReg)
      (rw0 := rw0) (rw1 := rw1) (rw2 := rw2) (rw3 := rw3) (rw4 := rw4) (rw5 := rw5)
      (Frame56 := ?frame56) hAlloc hFutDrop hstk hstk64 hrw0_ne3
      hpc4 hrun4 hsp4 hal4 hvregs_4 hinv4 htr4
      fun RoExtra sm6 hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 hfs6
          hx19_6 hx20_6 hx21_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 =>
        sepWPp_weaken_pre ?pre2
          (stage5_branch_after_reg_placed_ok
            (st0 := st0)
            (st := M.stepEvents (rustDeallocEvents 16 8)
              (M.stepEvents evsRegPoll (M.stepEvents evsRegShim st)))
            (dataPtr := dataPtr) (futPtr := futReg)
            (rw0 := rw0) (rw1 := rw1) (rw2 := rw2) (rw3 := rw3) (rw4 := rw4) (rw5 := rw5)
            (padVal := padVal) (w1_kyb := w1_kyb) (ans := ans) (kg := kg) (SpeH := SpeH)
            (Extra := Extra ∗ JunkRO1 ∗ RoExtra)
            hAlloc hRodataSaveSlot hSaveShim hSavePoll hPromote
            hRodataStoreSlot hStoreShim hStorePoll hFutDrop hDropSS
            (fun hAnsErr evsDrop hfree =>
              hEnvErr (hansReg'.symm.trans hAnsErr) futReg evsRegShim evsRegPoll evsDrop
                hboxRegShim hstRegPoll hfree)
            (fun reg hAnsOk =>
              hFitSaveShim reg (hansReg'.symm.trans hAnsOk) futReg evsRegShim evsRegPoll
                hboxRegShim hstRegPoll)
            (fun reg hAnsOk futSave evsSaveShim hboxSaveShim =>
              hFitSavePoll reg (hansReg'.symm.trans hAnsOk) futReg futSave
                evsRegShim evsRegPoll evsSaveShim hboxRegShim hstRegPoll hboxSaveShim)
            (fun reg hAnsOk futSave evsSaveShim evsSavePoll hboxSaveShim hstSavePoll =>
              hFitStoreShim reg (hansReg'.symm.trans hAnsOk) futReg futSave
                evsRegShim evsRegPoll evsSaveShim evsSavePoll
                hboxRegShim hstRegPoll hboxSaveShim hstSavePoll)
            (fun reg hAnsOk futSave futStore evsSaveShim evsSavePoll evsStoreShim
                hboxSaveShim hstSavePoll hboxStoreShim =>
              hFitStorePoll reg (hansReg'.symm.trans hAnsOk) futReg futSave futStore
                evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim
                hboxRegShim hstRegPoll hboxSaveShim hstSavePoll hboxStoreShim)
            (fun reg hAnsOk futSave futStore
                evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop
                hboxSaveShim hstSavePoll hboxStoreShim hstStorePoll hfree =>
              hEnvOk reg (hansReg'.symm.trans hAnsOk) futReg futSave futStore
                evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop
                hboxRegShim hstRegPoll hboxSaveShim hstSavePoll hboxStoreShim hstStorePoll hfree)
            hS hinitOk hstk hstk64 hs5
            halice hkgBytes hkemLen hkyberKey hekLen hkpkLen hfoldBundle
            hansReg' hrw0_ne3 hansBranch hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 hfs0
            (hfs6.trans hfs4') (hx19_6.trans hx19_4) (hx20_6.trans hx20_4)
            hx21_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hpost))
  case pre1 =>
    conv =>
      lhs
      simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
    exact Entails.of_eq (by dsimp only [fsp] at *; s5_ac_rfl)
  case pre2 =>
    conv => arg 1; dsimp only; simp only [sepConj_assoc]
    s5_have_eq hpScr :
        ((((fsp + 0x5c0#64) ↦₆₄ (fsp + 0x460#64)) ∗
          ((fsp + 0x5c8#64) ↦₆₄ futReg) ∗
          ((fsp + 0x5d0#64) ↦₆₄ lsρ idRegIdFutVtSym) ∗
          memRegion (fsp + 0x1600#64) 48) ∗ stage5ScratchRegRest fsp) ∗ ?remScr := by
      dsimp only [fsp] at *; s5_ac_rfl
    rw [← stage5ScratchAt_reg_split] at hpScr
    refine Entails.trans (Entails.of_eq hpScr) ?_
    s5_have_eq hpArgs :
        ((((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
          ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym)) ∗
          initArgsRegRestPlaced fsp x s0) ∗ ?remArgs := by
      dsimp only [fsp] at *; s5_ac_rfl
    rw [← initArgsAtPlaced_reg_split] at hpArgs
    refine Entails.trans (Entails.of_eq hpArgs) ?_
    s5_have_eq hpSt :
        (dirAt A.repAlloc x.stores StoresGhost.opened.identity.own ∗
          storesRegRest A.repAlloc x.stores StoresGhost.opened) ∗ ?remSt := by
      dsimp only [fsp] at *; s5_ac_rfl
    rw [← storesAt_reg_split] at hpSt
    refine Entails.trans (Entails.of_eq hpSt) ?_
    exact Entails.of_eq (by dsimp only [fsp] at *; s5_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlacedBudget

end
