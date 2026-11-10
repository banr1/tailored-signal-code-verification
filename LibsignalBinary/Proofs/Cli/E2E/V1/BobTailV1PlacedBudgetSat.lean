/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudgetSat

/-!
# `HookSat` Sibling of `BobTailV1PlacedBudget` (`BobTailV1PlacedBudgetSat`)

Provides the 4 closed `[LibsignalFullPlacement]` SPQR-V1 `initialize_bob_session`
(Block `75`) corollaries of `BobTailV1PlacedBudget` Section 5 re-typed over
`PqxdhPlacedHookContractsSat`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudgetSat

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalHooks
   blkPl_75 lsLogFilterAddr lsMemcpySym lsProg_75 lsmpl)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpyRegionSpec)
open CryptoVerification.E2E.Pqxdh.Initiator
  (AcceptKeysInput Bytes DRKey Primitives StructuralPrims WellSizedAcceptKeysInput)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto bobParamsFieldsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (PqxdhPlacedHookContractsSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudgetSat
  (pqxdhAccept_opt_fields_full_placed_ok_of_block_sat)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
  (BobSessionV1Post InitBobV1Env InitBobV1EnvOfEnv
   InitialStateMemInvPlacedOk InitialStateMemInvPlacedOkOfEnv
   hookSat_framelessMemcpy_of_sessionMemcpyRegionBudget
   hookSat_sessionShimBudget_of_noAllocShimBudget
   initializeBobSession_ok_v1_frozen_placed_of_accept_of_session)

private theorem hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm_local {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
    memcpyRegionSpec, allocMemcpyVmSpec] at hp ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), R, ?_, fun sf hq => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, by rwa [sepConj_assoc]⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0f, hacp.2.1⟩, by rwa [← sepConj_assoc]⟩

/-- Closed `[LibsignalFullPlacement]` budget-threaded SPQR-V1 `initialize_bob_session` (Block `75`)
discharging `h_accept` at `lsmpl.base 79` (`InitEnv`-parametric, `sessionMemcpyRegionBudgetSpec`). -/
public theorem initializeBobSession_ok_v1_full_placed_of_env_of_session_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st
      (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_frozen_placed_of_accept_of_session hWF
    (hookSat_sessionShimBudget_of_noAllocShimBudget hH.noAllocShim)
    hH.alloc hH.dealloc hmemcpy
    (pqxdhAccept_opt_fields_full_placed_ok_of_block_sat hWF hP hH
      (hookSat_framelessMemcpy_of_sessionMemcpyRegionBudget hmemcpy))
    hinit s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- Closed `[LibsignalFullPlacement]` budget-threaded SPQR-V1 `initialize_bob_session` (Block `75`)
at concrete `InitBobV1Env P F` (`sessionMemcpyRegionBudgetSpec`). -/
public theorem initializeBobSession_ok_v1_full_placed_of_session_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1Env P F s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) (InitialStateEnv F) s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_full_placed_of_env_of_session_sat hWF hP hH hmemcpy hinit
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_ok_v1_full_placed_of_env_of_session_sat`. -/
public theorem initializeBobSession_ok_v1_full_placed_of_env_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st
      (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) InitEnv s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_full_placed_of_env_of_session_sat hWF hP hH
    (hookSat_sessionMemcpyRegionBudget_of_allocMemcpyVm_local hmemcpy) hinit
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- `allocMemcpyVmSpec` convenience wrapper around `initializeBobSession_ok_v1_full_placed_of_session_sat`
at concrete `InitBobV1Env P F`. -/
public theorem initializeBobSession_ok_v1_full_placed_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P) (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F H)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp) (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (InitBobV1Env P F s0.sp inp drKey.pqrKey))
    (hrun : s0.status = ExecStatus.Running) (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true) (hpqr_ne : s0.sp - 576#64 ≠ 0#64)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr) (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr) (h_6 : inp.trustedPeer = true)
    (h_7 : inp.replayOk = true) (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp) (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (s0.readReg64 (.gpr 30#5)) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ Frame)
      (BobSessionV1Post A lim F (AcceptOptFieldsEnv P) (InitialStateEnv F) s0 st inp ikBPk spkBPk
        argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame) Qp :=
  initializeBobSession_ok_v1_full_placed_of_env_std_sat hWF hP hH hmemcpy hinit
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align hpqr_ne h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

end LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudgetSat
