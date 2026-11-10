/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Stage 5 Callee Call Combinators (`[LibsignalPlacement]`)

Budget-threaded `SepWPp` call combinators for Stage 5 session and store callees on
`initProgPlaced W` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget

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
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate hiding
  setUnackPreKeyMsgEpochInnerSpec idOwnShimSpecPlaced idRegIdPollSpecPlaced
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (sepWPp_weaken_pre sepWPp_pure_left sepWPp_exists_left)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas hiding
  s5_call_raw_placed s5_dealloc_ok_at_placed s5_memcpy_ok_at_placed s5_call_futDrop_placed
  s5_call_dealloc_placed s5_call_dropSS_placed
  s5_call_setUnackMsg_placed s5_call_setUnackKyb_placed s5_call_idRegIdShim_placed
  s5_call_idRegIdPoll_placed s5_call_idSaveShim_placed s5_call_idSavePoll_placed
  s5_call_memcpy_placed s5_call_promoteState_placed s5_call_sessStoreShim_placed
  s5_call_sessStorePoll_placed
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (VmPreserved AllocEvent AllocCostModel BudgetLimits FitsEvents FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget (setUnackKyberPreKeyIdBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
  (setUnackPreKeyMsgEpochEvents SetUnackPreKeyMsgEpochEnv fitsEnv_setUnackPreKeyMsgEpochEnv_iff
   setUnackPreKeyMsgEpochInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (idOwnShimSpecPlaced idRegIdPollSpecPlaced idSaveShimSpecPlaced idSavePollSpecPlaced
   sessStoreShimSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
  (s5_call_raw_placed)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InitTraceFsSound traceFsSound_initPlaced)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

/-- `VmPreserved`-strengthened contract for allocator-free `<SessionRecord>::promote_state` on empty
archived session map (`Pqxdh.ResponderStore.promoteStateEmptySpec`). -/
def promoteStateEmptyBudgetSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved Pqxdh.ResponderStore.promoteStateEmptySpec

/-! ## Typed `SepWPp` Call Combinators -/

theorem s5_call_setUnackMsg_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (setUnackPreKeyMsgEpochInnerSpec A lim)))
    (fsp : BitVec 64) (g : Pqxdh.TopLevel.SetUnackExactGhost) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = g.optOpkTag)
    (hx2 : (s.readReg64 .x2).setWidth 32 = g.optOpkVal)
    (hx3 : (s.readReg64 .x3).setWidth 32 = g.spkId)
    (hx4 : s.readReg64 .x4 = g.baseKeyPtr)
    (hx5 : s.readReg64 .x5 = 0#64)
    (hx6 : (s.readReg64 .x6).setWidth 32 = 0#32)
    (hbLen : g.baseKeyBytes.length = 32)
    (hfit : FitsEvents M lim st setUnackPreKeyMsgEpochEvents)
    (hpre : P ⊢ ((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (fsp - 144#64) (allocHookStack + 32) ∗
      cells (fsp - 144#64) 18 ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        (((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
          Pqxdh.Initiator.vecU8 A.repAlloc (g.statePtr + 0xf8#64)
            (Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC g.baseKeyBytes)) ∗
          ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
          ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
          ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
          ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
          memRegion (g.statePtr + 0x124#64) 4 ∗
          stackAt (fsp - 144#64) (allocHookStack + 32) ∗
          cells (fsp - 144#64) 18 ∗
          A.pool lim (M.stepEvents setUnackPreKeyMsgEpochEvents st) sm) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (g, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      dsimp only [setUnackPreKeyMsgEpochInnerSpec]
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx5, hx6⟩
        (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbLen, hfit⟩ (Entails.refl _))))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  dsimp only [setUnackPreKeyMsgEpochInnerSpec]
  simp only [hsp, sepConj_assoc]
  apply sepWPp_pure_left; intro htrm
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm (htrm.trans htr) (hfs htrm))

theorem s5_call_setUnackMsg_env_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (setUnackPreKeyMsgEpochInnerSpec A lim)))
    (fsp : BitVec 64) (g : Pqxdh.TopLevel.SetUnackExactGhost) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = g.optOpkTag)
    (hx2 : (s.readReg64 .x2).setWidth 32 = g.optOpkVal)
    (hx3 : (s.readReg64 .x3).setWidth 32 = g.spkId)
    (hx4 : s.readReg64 .x4 = g.baseKeyPtr)
    (hx5 : s.readReg64 .x5 = 0#64)
    (hx6 : (s.readReg64 .x6).setWidth 32 = 0#32)
    (hbLen : g.baseKeyBytes.length = 32)
    (hfit : FitsEnv M lim st SetUnackPreKeyMsgEpochEnv)
    (hpre : P ⊢ ((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (fsp - 144#64) (allocHookStack + 32) ∗
      cells (fsp - 144#64) 18 ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        (((g.baseKeyPtr ↦ₛ Pqxdh.Initiator.bytesToBv8 g.baseKeyBytes) ∗
          Pqxdh.Initiator.vecU8 A.repAlloc (g.statePtr + 0xf8#64)
            (Pqxdh.Initiator.bytesToBv8 (SignalPqxdh.encodeEC g.baseKeyBytes)) ∗
          ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
          ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
          ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
          ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
          memRegion (g.statePtr + 0x124#64) 4 ∗
          stackAt (fsp - 144#64) (allocHookStack + 32) ∗
          cells (fsp - 144#64) 18 ∗
          A.pool lim (M.stepEvents setUnackPreKeyMsgEpochEvents st) sm) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom :=
  s5_call_setUnackMsg_placed hcall fsp g st F hpc hrun hsp hsp_align hlr htr hcrl
    hx0 hx1 hx2 hx3 hx4 hx5 hx6 hbLen
    ((fitsEnv_setUnackPreKeyMsgEpochEnv_iff M lim st).mp hfit)
    hpre hnext

theorem s5_call_setUnackKyb_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl setUnackKyberPreKeyIdBudgetSpec))
    (fsp statePtr cap : BitVec 64) (w0 kpkId : BitVec 32) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = kpkId)
    (hcap : cap + 1#64 ≠ 0#64)
    (hpre : P ⊢ (((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ w0)) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files → VmPreserved s sm →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ kpkId)) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (statePtr, cap, kpkId) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      dsimp only [setUnackKyberPreKeyIdBudgetSpec, withVmPreserved, Pqxdh.setUnackKyberPreKeyIdSpec]
      simp only [sepConj_assoc]
      refine Entails.pure_right ⟨hx0, hx1, hcap⟩ ?_
      exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right w0 (Entails.refl _)))))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  dsimp only [setUnackKyberPreKeyIdBudgetSpec, withVmPreserved, Pqxdh.setUnackKyberPreKeyIdSpec]
  simp only [sepConj_assoc]
  apply sepWPp_pure_left; intro hvmm
  apply sepWPp_pure_left; intro htrm
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm (htrm.trans htr) (hfs htrm) hvmm)

theorem s5_call_setUnackKyb_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl setUnackKyberPreKeyIdBudgetSpec))
    (fsp statePtr cap : BitVec 64) (w0 kpkId : BitVec 32) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = statePtr)
    (hx1 : (s.readReg64 .x1).setWidth 32 = kpkId)
    (hcap : cap + 1#64 ≠ 0#64)
    (hpre : P ⊢ (((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ w0) ∗
      A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((((statePtr + 0x128#64) ↦₆₄ cap) ∗ ((statePtr + 0x140#64) ↦₃₂ kpkId) ∗
          A.pool lim st sm) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_setUnackKyb_placed hcall fsp statePtr cap w0 kpkId (A.pool lim st s ∗ F)
    hpc hrun hsp hsp_align hlr htr hcrl hx0 hx1 hcap
    (Entails.trans hpre (Entails.of_eq (by ac_rfl))) ?_
  intro sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm hvmm
  rw [← A.pool_of_vmPreserved hvmm]
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm)

theorem s5_call_idRegIdShim_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 603)
      (idOwnShimSpecPlaced idRegIdFutVtSym A lim (stk - cliInitiateFrame)))
    (fsp self : BitVec 64) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 603)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = self)
    (hfit : FitsEnv M lim st (BoxAllocEnv 16))
    (hpre : P ⊢ (A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      BoxAllocEnv 16 evs →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = lsρ idRegIdFutVtSym →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((A.live (sm.readReg64 .x0) 16 8 ∗
          idOwnFutBoxAt (sm.readReg64 .x0) self 0#8 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  unfold idOwnShimSpecPlaced at hcall
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (self, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hfit⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro evs
  apply sepWPp_pure_left; rintro ⟨hx1m, hnz, hal8, htrm, hevs⟩
  exact sepWPp_weaken_pre (Entails.of_eq (by dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt]; ac_rfl))
    (hnext sm evs hevs hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm
      (htrm.trans htr) (hfs htrm) hx1m hnz hal8)

theorem s5_call_idRegIdPoll_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {PollEnv : FsFiles → IdOwnPollGhostPlaced → List AllocEvent → Prop}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 568)
      (idRegIdPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (stk - cliInitiateFrame)))
    (fsp : BitVec 64) (g : IdOwnPollGhost) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 568)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.fut)
    (hx8 : s.readReg64 .x8 = g.out)
    (hpathLt : g.own.path.length < 2 ^ 32)
    (hpathOk : cliWrOk (pathOf g.own.path (utf8 "registration-id")))
    (hfit : FitsEnv M lim st (PollEnv s.fs.files ⟨g.fut, g.out, g.self, g.own⟩))
    (hpre : P ⊢ (idOwnFutBoxAt g.fut g.self 0#8 ∗ dirAt A.repAlloc g.self g.own ∗
      memRegion g.out 48 ∗ A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (ans : Except Unit (BitVec 32)),
      PollEnv s.fs.files ⟨g.fut, g.out, g.self, g.own⟩ evs →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      ans = (IdGhost.mk g.own (.new [])).regId cliIo.rd s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((idRegIdOutAt A.repAlloc g.out ans ∗ idOwnFutBoxAt g.fut g.self 1#8 ∗
          dirAt A.repAlloc g.self g.own ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  unfold idRegIdPollSpecPlaced at hcall
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (⟨g.fut, g.out, g.self, g.own⟩, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx8, hpathLt, hpathOk, hfit⟩
        (Entails.of_eq (by dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt]))))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro evs
  apply sepWPp_exists_left; intro ans
  apply sepWPp_pure_left; rintro ⟨hans, htrm, hevs⟩
  have houtEq : idRegIdOutAtPlaced A.repAlloc g.out ans = idRegIdOutAt A.repAlloc g.out ans := by
    cases ans <;> rfl
  rw [houtEq]
  exact sepWPp_weaken_pre (Entails.of_eq (by dsimp only [idOwnFutBoxAtPlaced, idOwnFutBoxAt]; ac_rfl))
    (hnext sm evs ans hevs hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm
      (htrm.trans htr) (hfs htrm) hans)

theorem s5_call_idSaveShim_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 600)
      (idSaveShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (fsp : BitVec 64) (c : IdentityShimCall) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 600)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = c.self)
    (hx1 : s.readReg64 .x1 = c.addrA)
    (hx2 : s.readReg64 .x2 = c.keyA)
    (hfit : FitsEnv M lim st (BoxAllocEnv 32))
    (hpre : P ⊢ (A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      BoxAllocEnv 32 evs →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = lsρ idSaveFutVtSym →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗
          idSaveBoxAt (sm.readReg64 .x0) c.self c.addrA c.keyA 0#8 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  unfold idSaveShimSpecPlaced at hcall
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (c, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx1, hx2, hfit⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro evs
  apply sepWPp_pure_left; rintro ⟨hx1m, hnz, hal8, htrm, hevs⟩
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm evs hevs hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm
      (htrm.trans htr) (hfs htrm) hx1m hnz hal8)

theorem s5_call_idSavePoll_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 565)
      (idSavePollSpecPlaced cliIo.rd cliWrOk A lim SaveEnv (stk - cliInitiateFrame)))
    (fsp : BitVec 64) (g : IdPollGhost) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 565)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.call.fut)
    (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hpathLt : g.peers.path.length < 2 ^ 32)
    (hchgLt : g.peers.changed.length < 2 ^ 32)
    (hpathOk : cliWrOk (pathOf g.peers.path g.call.call.addr.val.name))
    (hwf : ∀ bs, g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name = .ok bs → IdFileWf bs)
    (hfit : FitsEnv M lim st (SaveEnv s.fs.files g))
    (hpre : P ⊢ (idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 0#8 ∗
      dirAt A.repAlloc (g.self + 0x28#64) g.peers ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A.repAlloc g.call.call.addr g.call.call.addrA ∗
      (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗ FromRecordCallees.lsLogOff ∗
      A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (gr : Except Unit (List (BitVec 8)))
      (p : Except Unit (Option IdentityKey)),
      SaveEnv s.fs.files g evs →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      gr = g.peers.get cliIo.rd s.fs.files g.call.call.addr.val.name →
      IdPeerAns gr p →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((idSaveOutAt A.repAlloc g.call.out (idSaveOf p g.call.call.key) ∗
          dirAt A.repAlloc (g.self + 0x28#64)
            (idSavePeers g.peers g.call.call.addr.val.name g.call.call.key p) ∗
          idSaveBoxAt g.call.fut g.self g.call.call.addrA g.call.call.keyA 1#8 ∗
          protocolAddressAt A.repAlloc g.call.call.addr g.call.call.addrA ∗
          (g.call.call.keyA ↦ₛ g.call.call.key.publicKey.bytes.toList) ∗
          FromRecordCallees.lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  unfold idSavePollSpecPlaced at hcall
  have hLogEq : FromRecordCallees.lsLogOff = CryptoVerification.LibsignalTripleRatchet.lsLogOff :=
    rfl
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (g, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      simp only [hsp, hLogEq, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx8, hnameLt, hpathLt, hchgLt, hpathOk, hwf, hfit⟩
        (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro evs
  apply sepWPp_exists_left; intro gr
  apply sepWPp_exists_left; intro p
  apply sepWPp_pure_left; rintro ⟨⟨hgr, htrm⟩, hp, hevs⟩
  exact sepWPp_weaken_pre (Entails.of_eq (by rw [hLogEq]; ac_rfl))
    (hnext sm evs gr p hevs hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm
      (htrm.trans htr) (hfs htrm) hgr hp)

theorem s5_call_memcpy_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (fsp dst src : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpre : P ⊢ (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files → VmPreserved s sm →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (dst, src, bs) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      dsimp only [sessionMemcpyBudgetSpec]
      simp only [sessionMemcpySpec, libcMemcpySpec, stackAt, hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx1, hx2⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  dsimp only [sessionMemcpyBudgetSpec]
  simp only [sessionMemcpySpec, hsp, sepConj_assoc]
  apply sepWPp_pure_left; intro hvmm
  apply sepWPp_pure_left; rintro ⟨_, htrm⟩
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm (htrm.trans htr) (hfs htrm) hvmm)

theorem s5_call_memcpy_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (fsp dst src : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hpre : P ⊢ (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack ∗
      A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt fsp extHookStack ∗
          A.pool lim st sm) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_memcpy_placed hcall fsp dst src bs (A.pool lim st s ∗ F)
    hpc hrun hsp hsp_align hlr htr hcrl hx0 hx1 hx2
    (Entails.trans hpre (Entails.of_eq (by ac_rfl))) ?_
  intro sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm hvmm
  rw [← A.pool_of_vmPreserved hvmm]
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm)

theorem s5_call_promoteState_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec))
    (fsp recPtr srcPtr : BitVec 64) (bs : List (BitVec 8)) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = recPtr) (hx1 : s.readReg64 .x1 = srcPtr)
    (hbLen : bs.length = 344)
    (hpre : P ⊢ (((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (recPtr + 0x20#64) 336 ∗ (srcPtr ↦ₛ bs) ∗
      cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files → VmPreserved s sm →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((((recPtr + 0x18#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗
          cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (recPtr, srcPtr, bs) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      dsimp only [promoteStateEmptyBudgetSpec, withVmPreserved,
        Pqxdh.ResponderStore.promoteStateEmptySpec]
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx1, hbLen⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  dsimp only [promoteStateEmptyBudgetSpec, withVmPreserved,
    Pqxdh.ResponderStore.promoteStateEmptySpec]
  simp only [hsp, sepConj_assoc]
  apply sepWPp_pure_left; intro hvmm
  apply sepWPp_pure_left; intro htrm
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm (htrm.trans htr) (hfs htrm) hvmm)

theorem s5_call_promoteState_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl promoteStateEmptyBudgetSpec))
    (fsp recPtr srcPtr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = recPtr) (hx1 : s.readReg64 .x1 = srcPtr)
    (hbLen : bs.length = 344)
    (hpre : P ⊢ (((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (recPtr + 0x20#64) 336 ∗ (srcPtr ↦ₛ bs) ∗
      cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4 ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((((recPtr + 0x18#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗
          cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4 ∗
          A.pool lim st sm) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_promoteState_placed hcall fsp recPtr srcPtr bs (A.pool lim st s ∗ F)
    hpc hrun hsp hsp_align hlr htr hcrl hx0 hx1 hbLen
    (Entails.trans hpre (Entails.of_eq (by ac_rfl))) ?_
  intro sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm hvmm
  rw [← A.pool_of_vmPreserved hvmm]
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm)

theorem s5_call_sessStoreShim_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 605)
      (sessStoreShimSpecPlaced A lim (stk - cliInitiateFrame)))
    (fsp : BitVec 64) (c : StoreShimCall) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 605)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = c.self)
    (hx1 : s.readReg64 .x1 = c.addrA)
    (hx2 : s.readReg64 .x2 = c.recA)
    (hfit : FitsEnv M lim st (BoxAllocEnv 32))
    (hpre : P ⊢ (A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      BoxAllocEnv 32 evs →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      sm.readReg64 .x1 = lsρ sessStoreFutVtSym →
      sm.readReg64 .x0 ≠ 0#64 → (sm.readReg64 .x0).toNat % 8 = 0 →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((A.live (sm.readReg64 .x0) 32 8 ∗
          sessStoreBoxAt (sm.readReg64 .x0) c.self c.addrA c.recA 0#8 ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  unfold sessStoreShimSpecPlaced at hcall
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (c, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx1, hx2, hfit⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro evs
  apply sepWPp_pure_left; rintro ⟨hx1m, hnz, hal8, htrm, hevs⟩
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm evs hevs hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm
      (htrm.trans htr) (hfs htrm) hx1m hnz hal8)

theorem s5_call_sessStorePoll_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {StoreEnv : SessStorePollGhost → List AllocEvent → Prop}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim StoreEnv (stk - cliInitiateFrame)))
    (fsp : BitVec 64) (g : SessStorePollGhost) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 570)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = g.call.fut)
    (hx8 : s.readReg64 .x8 = g.call.out)
    (hnameLt : g.call.call.addr.name.bytes.length < 2 ^ 32)
    (hencLt : (E2E.Record.encodeRecord g.call.call.record).length < 2 ^ 32)
    (hchgLt : g.dir.changed.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (StoreEnv g))
    (hpre : P ⊢ (sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 0#8 ∗
      dirAt A.repAlloc g.self g.dir ∗ memRegion g.call.out 48 ∗
      protocolAddressAt A.repAlloc g.call.call.addr g.call.call.addrA ∗
      sessionRecordAt A.repAlloc g.call.call.recA g.call.call.g g.call.call.record ∗
      A.pool lim st s ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      StoreEnv g evs →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((sessStoreBoxAt g.call.fut g.self g.call.call.addrA g.call.call.recA 1#8 ∗
          dirAt A.repAlloc g.self (g.dir.put (addressText g.call.call.addr.val)
            (E2E.Record.encodeRecord g.call.call.record)) ∗
          (g.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (g.call.out + 8#64) 40 ∗
          protocolAddressAt A.repAlloc g.call.call.addr g.call.call.addrA ∗
          sessionRecordAt A.repAlloc g.call.call.recA g.call.call.g g.call.call.record ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt fsp (stk - cliInitiateFrame)) ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  unfold sessStorePollSpecPlaced at hcall
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (g, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx8, hnameLt, hencLt, hchgLt, hfit⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro evs
  apply sepWPp_pure_left; rintro ⟨htrm, hevs⟩
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm evs hevs hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm
      (htrm.trans htr) (hfs htrm))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.ScratchAndStoreCallsPlacedBudget
end
