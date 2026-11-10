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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ModelBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Stage 5 Registration-ID Future Drop and Branch (`[LibsignalPlacement]`)

Verifies `stage5_reg_drop_dealloc_placed_ok` (`+0x14e4..+0x1630`) and
`stage5_branch_after_reg_placed_ok` (`+0x1634`) on `initProgPlaced W` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget

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
  stage5_reg_drop_dealloc_placed_ok stage5_branch_after_reg_placed_ok
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced idSaveShimSpecPlaced idSavePollSpecPlaced
   sessStoreShimSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced initSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
  (s5_call_futDrop_pool_placed s5_call_dealloc_placed s5_dealloc_ok_at_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget
  (stage5_err_cleanup_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailStorePlacedBudget
  (sepWPp_step_to_lscro_vm_mem_framed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.AcceptTailPlacedBudget
  (initAcceptSessionGhost initAcceptSession stage5_accept_placed_ok)
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

private theorem s5_with_rodata_oom {prog : Program} {ret : BitVec 64} {s : State}
    {RO P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : ∀ {X : SepProp}, s.mem ⊨ X → s.mem ⊨ (RO ∗ X))
    (hw : SepWPp prog ret s (RO ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hw R (by rw [sepConj_assoc]; exact hro hm) hL

/-- Ghost argument passed to `idSavePollSpecPlaced` on the accepted `regId` branch. -/
abbrev initIdSavePollGhost (x : InitGhost) (s0 : State) (futSave : BitVec 64) : IdPollGhost :=
  { call :=
      { call :=
          { addrA := x.peerA
            addr := x.peer
            keyA := x.bundleA + 0x78#64
            key := x.bundle.idKey }
        fut := futSave
        out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
    self := x.stores
    peers := StoresGhost.opened.identity.peers }

/-- Ghost argument passed to `sessStorePollSpecPlaced` on the accepted `regId` branch. -/
abbrev initSessStorePollGhost (x : InitGhost) (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (hdr : SignalPqxdh.HandshakeHdr) (dataPtr : BitVec 64) (opkId reg padVal w1_kyb : BitVec 32)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8))) (kg : TailVecGhost)
    (s0 : State) (futStore : BitVec 64) : SessStorePollGhost :=
  { call :=
      { call :=
          { addrA := x.peerA
            addr := x.peer
            recA := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x128#64
            g := ⟨0#64, 8#64,
                  some (initAcceptSessionGhost x hdr dataPtr opkId reg padVal w1_kyb sg kg)⟩
            record := ⟨some (initAcceptSession be kp hdr reg x.peer.val ss)⟩ }
        fut := futStore
        out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 0x1600#64 }
    self := x.stores + 0xf0#64
    dir := StoresGhost.opened.sessions }

/-- Budget-threaded Steps 5 & 6 (`+0x14e4 .. +0x1630`) on a minimal 12-atom spatial frame: loads
`rw0..rw5` into `x26, x27, x25, x28, x24, x21`, drops and deallocates the 16-byte registration-id
future box (`futDropBudgetSpec` + `rustCliDeallocBudgetExternSpecWithStack`), and folds the 6 sret
words back into `memRegion (fsp + 0x1600#64) 48`. -/
theorem stage5_reg_drop_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W] {B : RunBudgets} {st : M.σ}
    {fsp storesPtr futPtr rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64}
    {Frame56 : SepProp} {stk : Nat} {s0 s : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hrw0_ne3 : rw0 + 3#64 ≠ 0#64)
    (hpc : s.pc = initEntryPlaced + offAfterRegPoll)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hal : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hinv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (RoExtra : SepProp) (sm6 : State),
      sm6.pc = initEntryPlaced + offRegDeallocDone →
      sm6.status = .Running → sm6.sp = fsp →
      calleeSavedVRegs sm6 = calleeSavedVRegs s0 →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm6.mem →
      sm6.trace = s0.trace → sm6.fs.files = s.fs.files →
      sm6.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm6.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm6.readReg64 (.gpr 21#5) = rw5 →
      sm6.readReg64 (.gpr 24#5) = rw4 →
      sm6.readReg64 (.gpr 25#5) = rw2 →
      sm6.readReg64 (.gpr 26#5) = rw0 →
      sm6.readReg64 (.gpr 27#5) = rw1 →
      sm6.readReg64 (.gpr 28#5) = rw3 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm6
        (((fsp + 0x5c8#64) ↦₆₄ futPtr) ∗
          ((fsp + 0x5d0#64) ↦₆₄ lsρ idRegIdFutVtSym) ∗
          memRegion (fsp + 0x1600#64) 48 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 16 8) st) sm6 ∗
          stackAt fsp (stk - cliInitiateFrame) ∗ Frame56 ∗ RoExtra) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s
      (((fsp + 0x5c8#64) ↦₆₄ futPtr) ∗
        ((fsp + 0x5d0#64) ↦₆₄ lsρ idRegIdFutVtSym) ∗
        ((fsp + 0x1600#64) ↦₆₄ rw0) ∗ (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ rw1) ∗
        (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ rw2) ∗ (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ rw3) ∗
        (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ rw4) ∗ (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ rw5) ∗
        idOwnFutBoxAt futPtr storesPtr 1#8 ∗ A.live futPtr 16 8 ∗ A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Frame56) Q Qp oom := by
  have hDealloc := s5_dealloc_ok_at_placed hAlloc
  have hsretOffs := sret_word_offs fsp
  conv =>
    arg 4
    rw [hsretOffs.1, hsretOffs.2.1, hsretOffs.2.2.1, hsretOffs.2.2.2.1, hsretOffs.2.2.2.2,
        show fsp + 0x5c8#64 = fsp + 1480#64 by bv_omega,
        show fsp + 0x5d0#64 = fsp + 1488#64 by bv_omega]
    simp only [sepConj_assoc]
  apply s5_with_rodata_oom (idRegIdFut_drop_rodata_placed hinv)
  generalize hdrop : lsmpl.base 547 = dropAddr
  s5_have_eq hpRegStep5 :
      (((lsρ idRegIdFutVtSym) ↦₆₄ᵣ dropAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ rw0) ∗
        ((fsp + 5640#64) ↦₆₄ rw1) ∗ ((fsp + 5648#64) ↦₆₄ rw2) ∗ ((fsp + 5656#64) ↦₆₄ rw3) ∗
        ((fsp + 5664#64) ↦₆₄ rw4) ∗ ((fsp + 5672#64) ↦₆₄ rw5) ∗
        ((fsp + 1488#64) ↦₆₄ lsρ idRegIdFutVtSym) ∗
        ((fsp + 1480#64) ↦₆₄ futPtr)) ∗
      (idOwnFutBoxAt futPtr storesPtr 1#8 ∗ A.live futPtr 16 8 ∗ A.pool lim st s ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Frame56) := by
    s5_ac_rfl
  suffices hAfterDrop : ∀ (sm5 : State) (dAddr : BitVec 64) {P5 : SepProp},
      P5 = (((lsρ idRegIdFutVtSym) ↦₆₄ᵣ dAddr) ∗ ((fsp + 0x1600#64) ↦₆₄ rw0) ∗
        ((fsp + 5640#64) ↦₆₄ rw1) ∗ ((fsp + 5648#64) ↦₆₄ rw2) ∗ ((fsp + 5656#64) ↦₆₄ rw3) ∗
        ((fsp + 5664#64) ↦₆₄ rw4) ∗ ((fsp + 5672#64) ↦₆₄ rw5) ∗
        ((fsp + 1488#64) ↦₆₄ lsρ idRegIdFutVtSym) ∗
        ((fsp + 1480#64) ↦₆₄ futPtr)) ∗
      (idOwnFutBoxAt futPtr storesPtr 1#8 ∗ A.live futPtr 16 8 ∗ A.pool lim st sm5 ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Frame56) →
      sm5.pc = initEntryPlaced + offRegDealloc →
      sm5.status = .Running →
      sm5.sp = fsp →
      sm5.spAligned = true →
      sm5.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      sm5.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      sm5.readReg64 (.gpr 21#5) = rw5 →
      sm5.readReg64 (.gpr 22#5) = lsρ idRegIdFutVtSym →
      sm5.readReg64 (.gpr 23#5) = futPtr →
      sm5.readReg64 (.gpr 24#5) = rw4 →
      sm5.readReg64 (.gpr 25#5) = rw2 →
      sm5.readReg64 (.gpr 26#5) = rw0 →
      sm5.readReg64 (.gpr 27#5) = rw1 →
      sm5.readReg64 (.gpr 28#5) = rw3 →
      calleeSavedVRegs sm5 = calleeSavedVRegs s0 →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm5.mem →
      sm5.trace = s0.trace →
      sm5.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm5 P5 Q Qp oom by
    rw [initEntryPlaced_eq_blkPl] at hpc
    by_cases hdropNe : dropAddr = 0#64
    · apply sepWPp_step_to_lscro_vm_mem_framed hinv hpRegStep5 (mid := initEntryPlaced + offRegDealloc)
      · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterRegPoll, offRegDealloc] at hpc ⊢
        rw [initEntryPlaced_eq_blkPl]
        by_vm_steps (
          wp_steps
          simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hrw0_ne3,
            Bool.false_eq_true, ↓reduceIte]
          try wp_steps
          simp (config := { failIfUnchanged := false }) only [hdropNe,
            beq_self_eq_true, ↓reduceIte]
          try wp_steps
          apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
            (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
          exact ⟨state_exists_setMem _, rfl⟩)
      intro _ hvmp5 hinv5; clear hpRegStep5
      refine sepWPp_weaken_pre (by rw [← A.pool_of_vmPreserved hvmp5]; exact Entails.refl _) ?_
      exact hAfterDrop _ 0#64 rfl
        (by dsimp only [initEntryPlaced, offRegDealloc]; wp_norm_goal; try rfl)
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
        (by simpa [State.spAligned, wp_norm, arm64_norm, hsp] using hal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [calleeSavedVRegs, wp_norm, arm64_norm, hvregs])
        hinv5
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr])
        (by wp_norm_goal)
    · apply sepWPp_step_to_lscro_vm_mem_framed hinv hpRegStep5 (mid := dropAddr)
      · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterRegPoll] at hpc ⊢
        by_vm_steps (
          wp_steps
          simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hrw0_ne3,
            Bool.false_eq_true, ↓reduceIte]
          try wp_steps
          simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hdropNe,
            Bool.false_eq_true, ↓reduceIte]
          try wp_steps
          apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
            (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
          exact ⟨state_exists_setMem _, rfl⟩)
      intro _ hvmp5 hinv5; clear hpRegStep5; subst hdrop
      refine s5_call_futDrop_pool_placed (A := A) (lim := lim) (s0 := s0)
        (ret_pc := initEntryPlaced + offRegDealloc)
        hFutDrop fsp st ?stF5
        (by wp_norm_goal; try rfl) (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp])
        (by simpa [State.spAligned, wp_norm, arm64_norm] using hal)
        (by dsimp only [initEntryPlaced, offRegDealloc]; wp_norm_goal; try rfl)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr]) hinv5
        ?stPre5 ?_
      case stPre5 =>
        rw [A.pool_of_vmPreserved hvmp5]
        s5_close_frame
      intro sm5 hpc5 hrun5 hsp5 hal5 hcs5 hinv5 htr5 hfs5
      simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs] at hcs5
      rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, _, hvregs_5⟩
      refine sepWPp_weaken_pre (Entails.of_eq (by s5_ac_rfl))
        (hAfterDrop sm5 (lsmpl.base 547) rfl hpc5 hrun5 hsp5 hal5
          hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5
          hvregs_5 hinv5 htr5 hfs5)
  clear hpRegStep5
  intro sm5 dAddr P5 hP5Eq hpc5 hrun5 hsp5 hal5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hvregs_5 hinv5 htr5 hfs5
  subst hP5Eq
  apply s5_with_rodata_oom (idRegIdFut_size_rodata_placed hinv5)
  apply s5_with_rodata_oom (idRegIdFut_align_rodata_placed hinv5)
  conv => arg 4; simp only [sepConj_assoc]
  s5_have_eq hpStep6 :
      (((lsρ idRegIdFutVtSym + 8#64) ↦₆₄ᵣ 16#64) ∗
        ((lsρ idRegIdFutVtSym + 16#64) ↦₆₄ᵣ 8#64)) ∗ ?remStep6 := by
    s5_ac_rfl
  rw [initEntryPlaced_eq_blkPl] at hpc5
  apply sepWPp_step_to_lscro_vm_mem_framed hinv5 hpStep6 (mid := lsρ lsRustDeallocSymCli)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offRegDealloc, lsρ] at hpc5 hx22_5 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp6 hinv6; clear hpStep6
  have hboxMem := idOwnFutBoxAt_entails_memRegion16 futPtr storesPtr 1#8
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)]
    simp only [sepConj_assoc]
  refine s5_call_dealloc_placed (s0 := s0) (ret_pc := initEntryPlaced + offRegDeallocDone)
    hDealloc fsp futPtr 16 8 st ?eF6
    (by dsimp only [lsρ]; wp_norm_goal; try rfl) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp5])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal5)
    (by dsimp only [initEntryPlaced, offRegDeallocDone]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr5]) hinv6
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx23_5])
    (by wp_norm_goal) (by wp_norm_goal) ⟨layoutOk_16_8, by decide⟩
    ?ePre6 ?_
  case ePre6 =>
    rw [A.pool_of_vmPreserved hvmp6]
    s5_have_eq hpull :
        idOwnFutBoxAt futPtr storesPtr 1#8 ∗ ?restRegBox := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero, hsp5]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpull)
      (Entails.trans (sepConj_mono_left hboxMem) ?_)
    s5_close_frame
  intro sm6 hpc6 hrun6 hsp6 _hal6 hcs6 hinv6 htr6 hfs6
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_5, hx20_5, hx21_5, hx24_5, hx25_5,
    hx26_5, hx27_5, hx28_5, hvregs_5] at hcs6
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, _, _, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, _, hvregs_6⟩
  s5_rw_pre (s5_stackAt_sub_split fsp (extHook_le_stkSub hstk) (stkSub_hi hstk64)).symm
  have hw48 := words6_entails_memRegion48 (fsp + 0x1600#64) rw0 rw1 rw2 rw3 rw4 rw5
  have hsretSymm := sret_word_offs_symm fsp
  s5_have_eq hpW48 :
      (((fsp + 0x1600#64) ↦₆₄ rw0) ∗ (((fsp + 0x1600#64) + 0x08#64) ↦₆₄ rw1) ∗
        (((fsp + 0x1600#64) + 0x10#64) ↦₆₄ rw2) ∗ (((fsp + 0x1600#64) + 0x18#64) ↦₆₄ rw3) ∗
        (((fsp + 0x1600#64) + 0x20#64) ↦₆₄ rw4) ∗ (((fsp + 0x1600#64) + 0x28#64) ↦₆₄ rw5)) ∗
      ?remAfterReg48 := by
    conv =>
      lhs
      rw [hsretSymm.1, hsretSymm.2.1, hsretSymm.2.2.1, hsretSymm.2.2.2.1, hsretSymm.2.2.2.2]
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq hpW48) (sepConj_mono_left hw48)) ?_
  refine sepWPp_weaken_pre ?_
    (hnext ?roExtra sm6 hpc6 hrun6 hsp6 hvregs_6 hinv6 htr6 (hfs6.trans hfs5)
      hx19_6 hx20_6 hx21_6 hx24_6 hx25_6 hx26_6 hx27_6 hx28_6)
  conv =>
    lhs
    rw [show fsp + 1480#64 = fsp + 0x5c8#64 by bv_omega,
        show fsp + 1488#64 = fsp + 0x5d0#64 by bv_omega]
  exact Entails.of_eq (by s5_ac_rfl)

/-- Budget-threaded Step 7 (`+0x1634 .. +0x1638`): branches on `ans` (`cmn x26, #0x2; b.ne +0x1858`)
to `EpiloguePlacedBudget.stage5_err_cleanup_placed_ok` (`.error ()`) or
`AcceptTailPlacedBudget.stage5_accept_placed_ok` (`.ok reg`). -/
theorem stage5_branch_after_reg_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [InitTraceFsSound mmpl gh W]
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr dataPtr futPtr rw0 rw1 rw2 rw3 rw4 rw5 : BitVec 64}
    {opkId padVal w1_kyb : BitVec 32} {ans : Except Unit (BitVec 32)}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {kg : TailVecGhost}
    {BRest SpeH Extra : SepProp} {stk : Nat} {s0 s5 sm6 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
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
    (hEnvErr : ans = .error () → ∀ evsDrop, FreeOnlyEvs evsDrop →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents evsDrop st) = M.stepEvents evs st0)
    (hFitSaveShim : ∀ reg, ans = .ok reg → FitsEnv M lim st (BoxAllocEnv 32))
    (hFitSavePoll : ∀ reg, ans = .ok reg → ∀ (futSave : BitVec 64) (evsSaveShim : List AllocEvent),
      BoxAllocEnv 32 evsSaveShim →
      FitsEnv M lim (M.stepEvents evsSaveShim st)
        (SaveEnv x.F (initIdSavePollGhost x s0 futSave)))
    (hFitStoreShim : ∀ reg, ans = .ok reg →
      ∀ (futSave : BitVec 64) (evsSaveShim evsSavePoll : List AllocEvent),
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
      FitsEnv M lim
        (M.stepEvents (rustDeallocEvents 32 8)
          (M.stepEvents evsSavePoll (M.stepEvents evsSaveShim st)))
        (BoxAllocEnv 32))
    (hFitStorePoll : ∀ reg, ans = .ok reg →
      ∀ (futSave futStore : BitVec 64) (evsSaveShim evsSavePoll evsStoreShim : List AllocEvent),
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
      BoxAllocEnv 32 evsStoreShim →
      FitsEnv M lim
        (M.stepEvents evsStoreShim
          (M.stepEvents (rustDeallocEvents 32 8)
            (M.stepEvents evsSavePoll (M.stepEvents evsSaveShim st))))
        (StoreEnv
          (initSessStorePollGhost x be kp hdr dataPtr opkId reg padVal w1_kyb sg ss kg s0 futStore)))
    (hEnvOk : ∀ reg, ans = .ok reg →
      ∀ (futSave futStore : BitVec 64)
        (evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop : List AllocEvent),
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
                    (M.stepEvents evsSavePoll (M.stepEvents evsSaveShim st))))))) =
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
    (hansReg' : ans = StoresGhost.opened.identity.regId cliIo.rd x.F)
    (hrw0_ne3 : rw0 + 3#64 ≠ 0#64)
    (hansBranch : regAnsBranchProp A.repAlloc x.ret ans rw0 rw1 rw2 rw3 rw4 rw5 SpeH)
    (hpc6 : sm6.pc = initEntryPlaced + offRegDeallocDone)
    (hrun6 : sm6.status = .Running)
    (hsp6 : sm6.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame)
    (hvregs_6 : calleeSavedVRegs sm6 = calleeSavedVRegs s0)
    (hinv6 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm6.mem)
    (htr6 : sm6.trace = s0.trace) (hfs0 : s0.fs.files = x.F) (hfs6' : sm6.fs.files = x.F)
    (hx19_6 : sm6.readReg64 (.gpr 19#5) = x.ret)
    (hx20_6 : sm6.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64)
    (hx21_6 : sm6.readReg64 (.gpr 21#5) = rw5)
    (hx24_6 : sm6.readReg64 (.gpr 24#5) = rw4)
    (hx25_6 : sm6.readReg64 (.gpr 25#5) = rw2)
    (hx26_6 : sm6.readReg64 (.gpr 26#5) = rw0)
    (hx27_6 : sm6.readReg64 (.gpr 27#5) = rw1)
    (hx28_6 : sm6.readReg64 (.gpr 28#5) = rw3)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
    let pg : TailVecGhost :=
      { vec := ⟨33#64, dataPtr, (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize⟩
        tail := unpack32 opkFlag ++ unpack32 opkId ++ unpack64 0#64 ++
                  unpack32 x.bundle.spkId ++ unpack32 padVal }
    let kg' : TailVecGhost := { vec := kg.vec, tail := unpack32 x.bundle.kpkId ++ unpack32 w1_kyb }
    let sg₁ : SessionGhost := { sg with pending := some pg, kyber := some kg' }
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sm6
      (storesAt A.repAlloc x.stores StoresGhost.opened ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
        ((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗ ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
        ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
        ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest ∗
        coinsCursorAtPlaced x.coinsP x.coins 192 ∗
        SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ FromRecordCallees.lsLogOff ∗
        A.pool lim st sm6 ∗ initSaved s0 ∗
        memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗ initFreshRecAt fsp ∗
        memRegion (fsp + 0x148#64) 0x150 ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        sessionStateAt A.repAlloc (fsp + 0x460#64) sg₁ ss.setUnacknowledgedPreKeyMessage ∗
        ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
        stage5ScratchAt fsp (fsp + 0x460#64) futPtr (lsρ idRegIdFutVtSym) ∗
        SpeH ∗
        stackAt fsp (stk - cliInitiateFrame) ∗ Extra) Q Qp oom := by
  intro fsp opkFlag pg kg' sg₁
  cases ans with
  | error u =>
    cases u
    dsimp only [regAnsBranchProp] at hansBranch
    obtain ⟨hrw0_ne2, k, hfoldK⟩ := hansBranch
    have hx26_ne2 : sm6.readReg64 (.gpr 26#5) + 2#64 ≠ 0#64 := by
      rw [hx26_6]; exact hrw0_ne2
    have hrw0_neFD : rw0 ≠ 0xFFFFFFFFFFFFFFFD#64 := by
      intro h; exact hrw0_ne3 (by subst h; decide)
    rw [initEntryPlaced_eq_blkPl] at hpc6
    apply sepWPp_step_to_lscro_vm_mem_framed hinv6 (emp_sepConj _).symm
      (mid := initEntryPlaced + offErrEntry)
    · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offRegDeallocDone, offErrEntry] at hpc6 ⊢
      rw [initEntryPlaced_eq_blkPl]
      by_vm_steps (
        wp_steps
        simp (config := { failIfUnchanged := false }) only [beq_eq_false_iff_ne.mpr hx26_ne2,
          Bool.false_eq_true, ↓reduceIte]
        try wp_steps
        apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
          (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
        exact ⟨state_exists_setMem _, rfl⟩)
    intro _ hvmp7 hinv7
    have hansErr : S.initiate x.F x.peer.val x.me.val x.bundle x.coins = some none := by
      rw [hS]
      exact initDef_eq_some_none_of_regId_err hs5.bundleEq hs5.trustedOk hs5.kpOk hansReg'.symm
    have hscrMerge := scratch_merge fsp (fsp + 0x460#64) futPtr (lsρ idRegIdFutVtSym)
    refine sepWPp_weaken_pre ?_
      (stage5_err_cleanup_placed_ok (B := B) (kp := kp) (pqspkPtr := pqspkPtr) (opkId := opkId)
        (k := k) (sg' := sg₁) (ss' := ss.setUnacknowledgedPreKeyMessage)
        (SpeHeap := SpeH) (Extra := ?extraErr)
        hAlloc hDropSS (hEnvErr rfl) hstk hstk64 hekLen hkpkLen hansErr
        (by dsimp only [initEntryPlaced, offErrEntry]; wp_norm_goal; try rfl)
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp6])
        hs5.ctrl.spAligned
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hvregs_6])
        hinv7
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr6])
        hfs0 hfs6'
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_6]; exact hrw0_neFD)
        (by
          simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx26_6, hx27_6,
            hx25_6, hx28_6, hx24_6, hx21_6]
          exact hfoldK)
        hpost)
    rw [emp_sepConj, ← A.pool_of_vmPreserved hvmp7]
    s5_have_eq hpB :
        (((x.bundleA + 0x38#64) ↦₃₂ x.bundle.spkId) ∗
          ((x.bundleA + 0x68#64) ↦₃₂ x.bundle.kpkId) ∗
          ((x.bundleA + 0x78#64) ↦ₛ x.bundle.idKey.publicKey.bytes.toList) ∗
          ((x.bundleA + 0x98#64) ↦₃₂ x.bundle.regId) ∗ BRest) ∗ ?remErrB := by
      conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpB) (Entails.trans (sepConj_mono_left hfoldBundle) ?_)
    s5_have_eq hpS :
        stage5ScratchAt fsp (fsp + 0x460#64) futPtr (lsρ idRegIdFutVtSym) ∗ ?remErrS := by
      s5_ac_rfl
    refine Entails.trans (Entails.of_eq hpS) (Entails.trans (sepConj_mono_left hscrMerge) ?_)
    simp (config := { failIfUnchanged := false }) only [emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by s5_ac_rfl)
  | ok reg =>
    dsimp only [regAnsBranchProp] at hansBranch
    obtain ⟨rfl, hrw1, rfl⟩ := hansBranch
    rw [initEntryPlaced_eq_blkPl] at hpc6
    apply sepWPp_step_to_lscro_vm_mem_framed hinv6 (emp_sepConj _).symm
      (mid := initEntryPlaced + offSave)
    · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offRegDeallocDone, offSave] at hpc6 ⊢
      rw [initEntryPlaced_eq_blkPl]
      by_vm_steps (
        wp_steps
        simp (config := { failIfUnchanged := false }) only [hx26_6,
          show (0xFFFFFFFFFFFFFFFE#64 : BitVec 64) + 2#64 = 0#64 by decide,
          beq_self_eq_true, ↓reduceIte]
        try wp_steps
        apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
          (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
        exact ⟨state_exists_setMem _, rfl⟩)
    intro _ hvmp7 hinv7
    refine sepWPp_weaken_pre ?_
      (stage5_accept_placed_ok (B := B)
        (pqspkPtr := pqspkPtr) (dataPtr := dataPtr) (opkId := opkId)
        (padVal := padVal) (w1_kyb := w1_kyb)
        (w5c8 := futPtr) (w5d0 := lsρ idRegIdFutVtSym) (Extra := ?extraAcc)
        hAlloc hRodataSaveSlot hSaveShim hSavePoll hPromote
        hRodataStoreSlot hStoreShim hStorePoll hFutDrop hDropSS
        (hFitSaveShim reg rfl) (hFitSavePoll reg rfl)
        (hFitStoreShim reg rfl) (hFitStorePoll reg rfl) (hEnvOk reg rfl)
        hS hinitOk hstk hstk64
        hs5.bundleEq hs5.trustedOk hs5.kpOk hansReg'.symm hs5.opkIdEq
        hs5.keysOk hs5.initSessOk hs5.pqLen halice hkgBytes hkemLen hkyberKey
        hekLen hkpkLen hfoldBundle
        (by dsimp only [initEntryPlaced, offSave]; wp_norm_goal; try rfl)
        (by wp_norm_lhs)
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp6])
        hs5.ctrl.spAligned
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hvregs_6])
        hinv7
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr6])
        hfs0 hfs6'
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx19_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_6])
        (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx27_6, hrw1])
        hpost)
    rw [emp_sepConj, ← A.pool_of_vmPreserved hvmp7]
    dsimp only [storesAt]
    conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
    simp (config := { failIfUnchanged := false }) only [emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by s5_ac_rfl)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget

end
