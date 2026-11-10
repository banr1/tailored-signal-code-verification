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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EntryAndRegIdPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.SessionBridge
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Stage 5 Entry and Unacknowledged PreKey Metadata (`[LibsignalPlacement]`)

Transfers Blocks `33` (`set_unacknowledged_pre_key_message`) and `34`
(`set_unacknowledged_kyber_pre_key_id`) onto `initProgPlaced W` and proves Stage 5 entry
(`+0x1484 → lr`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EntryAndRegIdPlacedBudget

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
open CryptoVerification.SignalSession.Cli.RunSkeleton hiding RunHooksPlaced
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs hiding initSlotSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  RunHooksPlaced stage5MemPlaced setUnackPreKeyMsgEpochInnerSpec
  idOwnShimSpecPlaced idRegIdPollSpecPlaced
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
  initiate_stage5_placed_ok_impl
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget
  (setUnackKyberPreKeyIdBudgetSpec setUnackKyberPreKeyId_placed_ok)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv futDropBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
  (SetUnackPreKeyMsgEpochEnv setUnackPreKeyMsgEpochEvents setUnackPreKeyMsgEpochInnerSpec
   cliExternsPlaced_durationSinceEpochAlloc_budget_sat
   setUnackPreKeyMsg_exact_stack_epoch_placed_at_block setUnackPreKeyMsg_exact_stack_epoch_placed_ok_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced idOwnShimSpecPlaced idRegIdPollSpecPlaced
   idSaveShimSpecPlaced idSavePollSpecPlaced sessStoreShimSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced initSlotSpecPlaced stage5MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EpiloguePlacedBudget
  (sepWPp_step_to_lscro_vm_mem)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
  (promoteStateEmptyBudgetSpec s5_call_setUnackMsg_env_placed s5_call_setUnackKyb_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdDropPlacedBudget
  (initIdSavePollGhost initSessStorePollGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.RegIdBranchPlacedBudget
  (initIdRegIdPollGhostPlaced stage5_reg_and_branch_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced)

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

/-! ## Callee Transfer Helpers (`Blocks 33 & 34 → initProgPlaced W`) -/

theorem s5_setUnackMsg_ok_at_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 33)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (setUnackPreKeyMsgEpochInnerSpec A lim)) :=
  setUnackPreKeyMsg_exact_stack_epoch_placed_at_block
    (callerProg := initProgPlaced mmpl gh W) (i := 521)
    hh.sessionShim hh.rawAlloc hh.rawDealloc hh.sessionMemcpyRegion
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_durationSinceEpochAlloc_budget_sat mmpl W)) (by decide)

theorem s5_setUnackMsg_ok_of_cliAllocHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hA : LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.CliGhostAllocHooks M A lim gh) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 33)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (setUnackPreKeyMsgEpochInnerSpec A lim)) :=
  setUnackPreKeyMsg_exact_stack_epoch_placed_ok_cli
    (callerProg := initProgPlaced mmpl gh W) (i := 521)
    mmpl gh W hA (by decide)

theorem s5_setUnackKyb_ok_at_placed [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 34)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl setUnackKyberPreKeyIdBudgetSpec) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (calleeProg := CryptoVerification.lsProg_34 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
      (setUnackKyberPreKeyId_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (by decide) (by decide) (by decide)

/-! ## Stage 5 Entry (`+0x1484 → lr`) -/

/-- Budget-threaded Stage 5 implementation from `+0x1484` (`offEntry`) to `lr`. -/
theorem initiate_stage5_placed_ok_impl [LibsignalPlacement] {M : AllocCostModel}
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
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hSetUnackMsg : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 33)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (setUnackPreKeyMsgEpochInnerSpec A lim)))
    (hSetUnackKyb : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 34)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl setUnackKyberPreKeyIdBudgetSpec))
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
    (hFitUnackMsg : FitsEnv M lim st SetUnackPreKeyMsgEpochEnv)
    (hFitRegShim : FitsEnv M lim (M.stepEvents setUnackPreKeyMsgEpochEvents st) (BoxAllocEnv 16))
    (hFitRegPoll : ∀ (futReg : BitVec 64) (evsRegShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      FitsEnv M lim (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))
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
              (M.stepEvents evsRegPoll
                (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))) =
          M.stepEvents evs st0)
    (hFitSaveShim : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg : BitVec 64) (evsRegShim evsRegPoll : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      FitsEnv M lim
        (M.stepEvents (rustDeallocEvents 16 8)
          (M.stepEvents evsRegPoll
            (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))
        (BoxAllocEnv 32))
    (hFitSavePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave : BitVec 64) (evsRegShim evsRegPoll evsSaveShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      FitsEnv M lim
        (M.stepEvents evsSaveShim
          (M.stepEvents (rustDeallocEvents 16 8)
            (M.stepEvents evsRegPoll
              (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st)))))
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
                (M.stepEvents evsRegPoll
                  (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st)))))))
        (BoxAllocEnv 32))
    (hFitStorePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave futStore : BitVec 64)
        (evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
      BoxAllocEnv 32 evsStoreShim →
      ∀ (dataPtr : BitVec 64) (padVal w1_kyb : BitVec 32) (kg : TailVecGhost),
      FitsEnv M lim
        (M.stepEvents evsStoreShim
          (M.stepEvents (rustDeallocEvents 32 8)
            (M.stepEvents evsSavePoll
              (M.stepEvents evsSaveShim
                (M.stepEvents (rustDeallocEvents 16 8)
                  (M.stepEvents evsRegPoll
                    (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))))))
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
      ∀ (dataPtr : BitVec 64) (padVal w1_kyb : BitVec 32) (kg : TailVecGhost),
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
                          (M.stepEvents evsRegPoll
                            (M.stepEvents evsRegShim
                              (M.stepEvents setUnackPreKeyMsgEpochEvents st))))))))))) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (_hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
      (stage5MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
      Q Qp oom := by
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  have hfs0 : s0.fs.files = x.F := hs5.ctrl.files0.symm.trans hs5.files
  have hx19_0 : s5.readReg64 (.gpr 19#5) = x.ret := hs5.ctrl.x19.trans hs5.x8
  have halign_s5 : s5.spAligned = true := spAligned_fsp hs5.ctrl.spAligned hs5.ctrl.sp
  have hrun0 : s5.status = .Running := hs5.ctrl.run
  have hsp0 : s5.sp = fsp := hs5.ctrl.sp
  have hx20_0 : s5.readReg64 (.gpr 20#5) = fsp + 0x460#64 := hs5.x20
  obtain ⟨hekU8Len, hekEncEq, hkemLen, hkyberKey⟩ :=
    initiateKeys_hdr_props hs5.ekPairEq hs5.keysOk
  have hekLen : ekASk.length = 32 ∧ ekAPk.length = 32 := by
    let ekSeed : List.Vector (BitVec 8) 32 := ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    let ekKP := keyPairOf W.C ekSeed
    have hek : ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList :=
      hs5.ekPairEq
    exact ⟨hek.1 ▸ ekKP.privateKey.bytes.toList_length,
           hek.2 ▸ ekKP.publicKey.bytes.toList_length⟩
  have hpc0 : s5.pc = initEntryPlaced + offEntry := hs5.ctrl.pc
  conv =>
    arg 4
    unfold stage5MemPlaced
    dsimp only
    rw [show s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp from rfl]
    simp only [sepConj_assoc]
  s5_have_eq hpScr : memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗ ?scrRem := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq hpScr)
    (sepConj_mono_left (scratch_split fsp))) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro w5c0
  apply sepWPp_exists_left; intro w5c8
  apply sepWPp_exists_left; intro w5d0
  s5_have_eq hpBun :
      cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗ ?bunRem := by
    s5_ac_rfl
  refine s5_apply_lens_oom hpBun fun R m hm => ?_
  obtain ⟨BRest, hkpkLen, hmBun, hfoldBundle⟩ :=
    cliBundleAt_stage5_lens x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr R m hm
  simp only [← sepConj_assoc] at hmBun
  refine ⟨_, hmBun, ?_⟩
  obtain ⟨_, _, halice, hpend0, ⟨kg, hkyb0, hkgBytes⟩, _, _⟩ := hs5.canonPre
  s5_have_eq hpSS : sessionStateAt A.repAlloc (fsp + 0x460#64) sg ss ∗ ?ssRem := by
    s5_ac_rfl
  refine s5_apply_lens_oom hpSS fun R2 m2 hm2 => ?_
  obtain ⟨_, w0_kyb, w1_kyb, SSRest, rfl, hcapKybNe, hmSS, hfoldUnack⟩ :=
    sessionState_unack_lens A.repAlloc (fsp + 0x460#64) sg ss hpend0 hkyb0
      (pendBytes := (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize)
      (by dsimp only [PublicKey.serialize]; simp) R2 m2 hm2
  simp only [← sepConj_assoc] at hmSS
  refine ⟨_, hmSS, ?_⟩
  conv => arg 4; unfold initArgsAtPlaced; rw [stage3KeySlotsAt_unfold]; simp only [sepConj_assoc]
  rw [initEntryPlaced_eq_blkPl] at hpc0
  apply sepWPp_step_to_lscro_vm_mem hs5.ctrl.inv (mid := lsmpl.base 33)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offEntry] at hpc0 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp1 hinv1
  let opkFlag : BitVec 32 := if x.bundle.opk.isSome then 1#32 else 0#32
  let gUnack : Pqxdh.TopLevel.SetUnackExactGhost :=
    { statePtr := fsp + 0x460#64
      optOpkTag := opkFlag
      optOpkVal := opkId
      spkId := x.bundle.spkId
      baseKeyPtr := fsp + 0x298#64
      baseKeyBytes := toU8 ekAPk }
  conv =>
    arg 4
    rw [s5_stackAt_sub_split fsp (unack_le_stkSub hstk) (stkSub_hi hstk64),
        stackAt_split_setUnack fsp]
    simp only [sepConj_assoc]
  refine s5_call_setUnackMsg_env_placed (s0 := s0) (ret_pc := initEntryPlaced + offAfterUnackMsg)
    hSetUnackMsg fsp gUnack st ?eF1
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp0])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using halign_s5)
    (by dsimp only [initEntryPlaced, offAfterUnackMsg]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hs5.trace]) hinv1
    (by dsimp only [gUnack]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_0])
    (by dsimp only [gUnack, opkFlag]; wp_norm_goal)
    (by dsimp only [gUnack]; wp_norm_goal)
    (by dsimp only [gUnack]; wp_norm_goal)
    (by dsimp only [gUnack]; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp0])
    (by wp_norm_goal) (by wp_norm_goal)
    hekU8Len hFitUnackMsg ?ePre1 ?_
  case ePre1 =>
    rw [A.pool_of_vmPreserved hvmp1]
    inImageKitClearInvHyps
    dsimp only [gUnack]
    rw [bytesToBv8_toU8 ekAPk]
    s5_close_frame
  intro sm1 hpc1 hrun1 hsp1 hal1 hcs1 hinv1 htr1 hfs1
  have hfs1' : sm1.fs.files = x.F := hfs1.trans hs5.files
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_0, hx20_0, hs5.ctrl.vregs] at hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  s5_rw_pre (stackAt_split_setUnack fsp).symm
  s5_rw_pre (s5_stackAt_sub_split fsp (unack_le_stkSub hstk) (stkSub_hi hstk64)).symm
  rw [initEntryPlaced_eq_blkPl] at hpc1
  apply sepWPp_step_to_lscro_vm_mem hinv1 (mid := lsmpl.base 34)
  · dsimp only [initProgPlaced, initProgExtPlaced, lsProg_521, offAfterUnackMsg] at hpc1 ⊢
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr (by wp_norm_goal) (by wp_norm_lhs)
        (by simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm])
      simp (config := { failIfUnchanged := false }) only [wp_norm, arm64_norm]
      exact ⟨state_exists_setMem _, rfl⟩)
  intro _ hvmp2 hinv2
  refine s5_call_setUnackKyb_pool_placed (A := A) (lim := lim) (s0 := s0)
    (ret_pc := initEntryPlaced + offAfterUnackKyb)
    hSetUnackKyb fsp (fsp + 0x460#64) kg.vec.cap w0_kyb x.bundle.kpkId
    (M.stepEvents setUnackPreKeyMsgEpochEvents st) ?eF2
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hsp1])
    (by simpa [State.spAligned, wp_norm, arm64_norm] using hal1)
    (by dsimp only [initEntryPlaced, offAfterUnackKyb]; wp_norm_goal; try rfl)
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, htr1]) hinv2
    (by simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, hx20_1])
    (by wp_norm_goal) hcapKybNe
    ?ePre2 ?_
  case ePre2 =>
    rw [A.pool_of_vmPreserved hvmp2]
    s5_close_frame
  intro sm2 hpc2 hrun2 hsp2 _hal2 hcs2 hinv2 htr2 hfs2
  have hfs2' : sm2.fs.files = x.F := hfs2.trans hfs1'
  simp (config := { zetaDelta := false }) only [CalleeSavedPreserved, wp_norm, arm64_norm, hx19_1, hx20_1, hvregs_1] at hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  conv =>
    arg 4
    dsimp only [gUnack]
    try rw [bytesToBv8_toU8 ekAPk]
    try rw [hekEncEq]
  s5_have_eq hpUnackVec :
      (Pqxdh.Initiator.vecU8 A.repAlloc ((fsp + 0x460#64) + 0xf8#64)
        (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize ∗
       memRegion ((fsp + 0x460#64) + 0x124#64) 4) ∗ ?unackVecRem := by
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq hpUnackVec)
    (sepConj_mono_left (sepConj_mono_right (memRegion_4_entails_32 ((fsp + 0x460#64) + 0x124#64))))) ?_
  conv =>
    arg 4
    unfold Pqxdh.Initiator.vecU8
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepWPp_exists_left; intro padVal
  apply sepWPp_exists_left; intro dataPtr
  refine sepWPp_pure_left fun hdataNonNull => ?_
  have hssFolded := hfoldUnack opkFlag opkId x.bundle.spkId x.bundle.kpkId padVal dataPtr hdataNonNull
  s5_have_eq hpFoldSS :
      ((((fsp + 0x460#64) + 0xf8#64) ↦₆₄ 33#64) ∗
        (((fsp + 0x460#64) + 0x100#64) ↦₆₄ dataPtr) ∗
        (((fsp + 0x460#64) + 0x108#64) ↦₆₄ 33#64) ∗
        (dataPtr ↦ₛ (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize) ∗
        A.repAlloc.live dataPtr 33 1 ∗
        (((fsp + 0x460#64) + 0x110#64) ↦₃₂ opkFlag) ∗
        (((fsp + 0x460#64) + 0x114#64) ↦₃₂ opkId) ∗
        (((fsp + 0x460#64) + 0x118#64) ↦₆₄ 0#64) ∗
        (((fsp + 0x460#64) + 0x120#64) ↦₃₂ x.bundle.spkId) ∗
        (((fsp + 0x460#64) + 0x124#64) ↦₃₂ padVal) ∗
        (((fsp + 0x460#64) + 0x128#64) ↦₆₄ kg.vec.cap) ∗
        (((fsp + 0x460#64) + 0x140#64) ↦₃₂ x.bundle.kpkId) ∗ SSRest) ∗ ?afterFoldSS := by
    conv => lhs; simp (config := { zetaDelta := false }) only [
      show ((fsp + 0x460#64) + 0xf8#64) + 8#64 = (fsp + 0x460#64) + 0x100#64 by bv_omega,
      show ((fsp + 0x460#64) + 0xf8#64) + 16#64 = (fsp + 0x460#64) + 0x108#64 by bv_omega,
      show (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize.length = 33 by
        dsimp only [PublicKey.serialize]; simp,
      show BitVec.ofNat 64 33 = 33#64 from rfl]
    s5_ac_rfl
  refine sepWPp_weaken_pre (Entails.trans (Entails.of_eq hpFoldSS) (sepConj_mono_left hssFolded)) ?_
  refine sepWPp_weaken_pre ?_
    (stage5_reg_and_branch_placed_ok (st0 := st0)
      (st := M.stepEvents setUnackPreKeyMsgEpochEvents st)
      (dataPtr := dataPtr) (w5c0 := w5c0) (w5c8 := w5c8) (w5d0 := w5d0)
      (padVal := padVal) (w1_kyb := w1_kyb) (kg := kg) (Extra := emp)
      hAlloc hRodataRegIdSlot hRegShim hRegPoll hRodataSaveSlot hSaveShim hSavePoll
      hPromote hRodataStoreSlot hStoreShim hStorePoll hFutDrop hDropSS
      hFitRegShim hFitRegPoll hEnvErr hFitSaveShim hFitSavePoll hFitStoreShim
      (fun reg hOk futReg futSave futStore evsRegShim evsRegPoll evsSaveShim evsSavePoll
          evsStoreShim hb1 hp1 hb2 hp2 hb3 =>
        hFitStorePoll reg hOk futReg futSave futStore
          evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim
          hb1 hp1 hb2 hp2 hb3 dataPtr padVal w1_kyb kg)
      (fun reg hOk futReg futSave futStore evsRegShim evsRegPoll evsSaveShim evsSavePoll
          evsStoreShim evsStorePoll evsDrop hb1 hp1 hb2 hp2 hb3 hp3 hfree =>
        hEnvOk reg hOk futReg futSave futStore
          evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim evsStorePoll evsDrop
          hb1 hp1 hb2 hp2 hb3 dataPtr padVal w1_kyb kg hp3 hfree)
      hS hinitOk hstk hstk64 hs5
      halice hkgBytes hkemLen hkyberKey hekLen hkpkLen hfoldBundle
      hpc2 hrun2 hsp2 hvregs_2 hinv2 htr2 hfs0 hfs2' hx19_2 hx20_2 hpost)
  inImageKitClearInvHyps
  conv =>
    rhs
    dsimp only [initArgsAtPlaced]
    rw [show s0.sp - BitVec.ofNat 64 cliInitiateFrame = fsp from rfl, stage3KeySlotsAt_unfold,
        show A.repAlloc.live pqspkPtr 1568 1 = A.live pqspkPtr 1568 1 from rfl]
    simp only [sepConj_emp, sepConj_assoc]
  conv =>
    rhs
    pattern ((fsp + 0x300#64) ↦₃₂ _)
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm]
  conv =>
    rhs
    pattern ((fsp + 0x438#64) ↦₈ _)
    simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm]
  conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [BitVec.add_zero]
  exact Entails.of_eq (by dsimp only [fsp] at *; s5_ac_rfl)

/-- Stage 5 implementation discharging `hAlloc` and Blocks `33` and `34` directly from
`RunHooksPlaced`. -/
theorem initiate_stage5_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {RegPollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
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
    (hFitUnackMsg : FitsEnv M lim st SetUnackPreKeyMsgEpochEnv)
    (hFitRegShim : FitsEnv M lim (M.stepEvents setUnackPreKeyMsgEpochEvents st) (BoxAllocEnv 16))
    (hFitRegPoll : ∀ (futReg : BitVec 64) (evsRegShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      FitsEnv M lim (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))
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
              (M.stepEvents evsRegPoll
                (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))) =
          M.stepEvents evs st0)
    (hFitSaveShim : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg : BitVec 64) (evsRegShim evsRegPoll : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      FitsEnv M lim
        (M.stepEvents (rustDeallocEvents 16 8)
          (M.stepEvents evsRegPoll
            (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))
        (BoxAllocEnv 32))
    (hFitSavePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave : BitVec 64) (evsRegShim evsRegPoll evsSaveShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      FitsEnv M lim
        (M.stepEvents evsSaveShim
          (M.stepEvents (rustDeallocEvents 16 8)
            (M.stepEvents evsRegPoll
              (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st)))))
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
                (M.stepEvents evsRegPoll
                  (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st)))))))
        (BoxAllocEnv 32))
    (hFitStorePoll : ∀ reg, StoresGhost.opened.identity.regId cliIo.rd x.F = .ok reg →
      ∀ (futReg futSave futStore : BitVec 64)
        (evsRegShim evsRegPoll evsSaveShim evsSavePoll evsStoreShim : List AllocEvent),
      BoxAllocEnv 16 evsRegShim →
      RegPollEnv x.F (initIdRegIdPollGhostPlaced x s0 futReg) evsRegPoll →
      BoxAllocEnv 32 evsSaveShim →
      SaveEnv x.F (initIdSavePollGhost x s0 futSave) evsSavePoll →
      BoxAllocEnv 32 evsStoreShim →
      ∀ (dataPtr : BitVec 64) (padVal w1_kyb : BitVec 32) (kg : TailVecGhost),
      FitsEnv M lim
        (M.stepEvents evsStoreShim
          (M.stepEvents (rustDeallocEvents 32 8)
            (M.stepEvents evsSavePoll
              (M.stepEvents evsSaveShim
                (M.stepEvents (rustDeallocEvents 16 8)
                  (M.stepEvents evsRegPoll
                    (M.stepEvents evsRegShim (M.stepEvents setUnackPreKeyMsgEpochEvents st))))))))
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
      ∀ (dataPtr : BitVec 64) (padVal w1_kyb : BitVec 32) (kg : TailVecGhost),
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
                          (M.stepEvents evsRegPoll
                            (M.stepEvents evsRegShim
                              (M.stepEvents setUnackPreKeyMsgEpochEvents st))))))))))) =
          M.stepEvents evs st0)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hs5 : AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s5
      (stage5MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0 s5)
      Q Qp oom := by
  letI : InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  exact initiate_stage5_placed_ok_impl hh.alloc (s5_setUnackMsg_ok_at_placed hh)
    (s5_setUnackKyb_ok_at_placed mmpl gh W) hRodataRegIdSlot hRegShim hRegPoll
    hRodataSaveSlot hSaveShim hSavePoll hPromote hRodataStoreSlot hStoreShim hStorePoll
    hFutDrop hDropSS hFitUnackMsg hFitRegShim hFitRegPoll hEnvErr hFitSaveShim hFitSavePoll
    hFitStoreShim hFitStorePoll hEnvOk hS hinitOk hcoinsLt hstk hstk64 hs5 hpost

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EntryAndRegIdPlacedBudget

end
