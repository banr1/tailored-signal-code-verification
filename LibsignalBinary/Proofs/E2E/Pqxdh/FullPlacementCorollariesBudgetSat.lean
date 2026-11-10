/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedBBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget

/-!
# `HookSat` Sibling of `FullPlacementCorollariesBudget` (`FullPlacementCorollariesBudgetSat`)

Provides the 12 `[LibsignalFullPlacement]` budget-threaded corollaries of
`FullPlacementCorollariesBudget` re-typed over `PqxdhPlacedHookContractsSat` (replacing
the `memset` hook equality inside `HkdfPlacedHooks` with
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudgetSat

open Arm64 ProofLib SepProp BitVec
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks
   blkPl_75 lsLogFilterAddr lsMemcpySym lsProg_75 lsmpl)
open CryptoVerification.E2E.Pqxdh.Initiator
  (AcceptKeysInput Bytes DRKey Primitives StructuralPrims WellSizedAcceptKeysInput
   bytesToBv8 pqxdhEntryStack)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (BobCutPost PrimitivesMatchCrypto
   bobFrameAtSpqr bobParamsFieldsAt bobSpqrCutCells initBobSavedRegs pqxdhAcceptOptFieldsAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpySpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlacedBudget
  (vecAppendElements_fast_placed_ok_cl)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
  (pqxdhAcceptOptFieldsFrozenPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedBBudget
  (pqxdhAccept_opt_fields_placed_ok_of_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlacedBudget
  (pqxdhAcceptErrOwnedFrozenPlacedSpec pqxdhAccept_err_owned_placed_ok_of_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
  (hookSat_framelessMemcpy_of_allocMemcpyVm)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (PqxdhPlacedHookContractsSat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
  (initBob_to_spqr_full_frozen_placed_of_accept
   initializeBobSessionErrFrozenPlacedSpec
   initializeBobSession_cut_frozen_placed_of_accept
   initializeBobSession_err_frozen_placed_ok_of_accept)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
  (initializeBobSessionErrOwnedFrozenPlacedSpec
   initializeBobSession_err_owned_frozen_placed_ok_of_accept)
open LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget
  (ecPubKeyIsCanonical_placed_ok_cl)

/-- Closed `[LibsignalFullPlacement]` budget-threaded contract for `Pqxdh::accept` (Block `79`)
lifted to any `callerProg` (`[IsLsBlockProg callerProg i H]`) at `lsmpl.base 79` from
`PqxdhPlacedHookContractsSat` and `HookSat H lsMemcpySym framelessMemcpySpec`. -/
public theorem pqxdhAccept_opt_fields_full_placed_ok_of_block_sat [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_opt_fields_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (vecAppendElements_fast_placed_ok_cl h_memcpy)
    (hH.hkdfExtract_ok hP)
    (hH.hkdfExpandMultiInfo_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.kyberDecaps

/-- `allocMemcpyVmSpec` convenience wrapper around
`pqxdhAccept_opt_fields_full_placed_ok_of_block_sat`. -/
public theorem pqxdhAccept_opt_fields_full_placed_ok_of_block_std_sat [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_opt_fields_full_placed_ok_of_block_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting contract for
`Pqxdh::accept` (Block `79`) lifted to any `callerProg` at `lsmpl.base 79`. -/
public theorem pqxdhAccept_err_owned_full_placed_ok_of_block_sat [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_err_owned_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy

/-- `allocMemcpyVmSpec` convenience wrapper around
`pqxdhAccept_err_owned_full_placed_ok_of_block_sat`. -/
public theorem pqxdhAccept_err_owned_full_placed_ok_of_block_std_sat [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {P : Primitives} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  pqxdhAccept_err_owned_full_placed_ok_of_block_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded rejecting run of `initialize_bob_session`
(Block `75`) on `lsProg_75 H`. -/
public theorem initializeBobSession_err_full_placed_ok_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_frozen_placed_ok_of_accept
    (pqxdhAccept_opt_fields_full_placed_ok_of_block_sat hWF hP hH h_memcpy)

/-- `allocMemcpyVmSpec` convenience wrapper around `initializeBobSession_err_full_placed_ok_sat`. -/
public theorem initializeBobSession_err_full_placed_ok_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_full_placed_ok_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded owned-error rejecting run of
`initialize_bob_session` (Block `75`) on `lsProg_75 H`. -/
public theorem initializeBobSession_err_owned_full_placed_ok_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_owned_frozen_placed_ok_of_accept
    (pqxdhAccept_err_owned_full_placed_ok_of_block_sat hWF hP hH h_memcpy)

/-- `allocMemcpyVmSpec` convenience wrapper around
`initializeBobSession_err_owned_full_placed_ok_sat`. -/
public theorem initializeBobSession_err_owned_full_placed_ok_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P)) :=
  initializeBobSession_err_owned_full_placed_ok_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)

/-- Closed `[LibsignalFullPlacement]` budget-threaded frame-retaining cut of
`initialize_bob_session` (Block `75`) from entry to `spqr::initial_state` (`lsmpl.base 327`) for
SPQR-V1 `BobTailV1`. -/
public theorem initBob_to_spqr_full_placed_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, AcceptOptFieldsEnv P inp evs ∧
          (P_f ⊢
            bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
              spkBPk inp.spkBSk ∗
            bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame)) ∧
        LibsignalFrozen lsmpl sf.mem ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) = (blkPl_75).base + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp :=
  initBob_to_spqr_full_frozen_placed_of_accept hWF
    (pqxdhAccept_opt_fields_full_placed_ok_of_block_sat hWF hP hH h_memcpy)
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- `allocMemcpyVmSpec` convenience wrapper around `initBob_to_spqr_full_placed_sat`. -/
public theorem initBob_to_spqr_full_placed_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (fun sf P_f =>
        (∃ evs : List AllocEvent, AcceptOptFieldsEnv P inp evs ∧
          (P_f ⊢
            bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
              spkBPk inp.spkBSk ∗
            bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
            (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
            pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
            ((argPtr + 297#64) ↦₈ 0#8) ∗
            memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt (s0.sp - 768#64) pqxdhEntryStack ∗
            A.pool lim (M.stepEvents evs st) sf ∗ Frame)) ∧
        LibsignalFrozen lsmpl sf.mem ∧
        sf.status = ExecStatus.Running ∧ sf.sp = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 0#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 8#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 19#5) = outPtr ∧
        sf.readReg64 (.gpr 20#5) = ratchetKeyPairPtr ∧
        sf.readReg64 (.gpr 21#5) = argPtr ∧
        sf.readReg64 (.gpr 23#5) = s0.sp - 768#64 ∧
        sf.readReg64 (.gpr 27#5) = s0.sp - 488#64 ∧
        sf.readReg64 (.gpr 30#5) = (blkPl_75).base + 252#64 ∧
        sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0)
      Qp :=
  initBob_to_spqr_full_placed_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)
    s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- Closed `[LibsignalFullPlacement]` budget-threaded `BobCutPost` cut of `initialize_bob_session`
(Block `75`) at `spqr::initial_state` (`lsmpl.base 327`). -/
public theorem initializeBobSession_cut_full_placed_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      Qp :=
  initializeBobSession_cut_frozen_placed_of_accept hWF
    (pqxdhAccept_opt_fields_full_placed_ok_of_block_sat hWF hP hH h_memcpy)
    s0 st inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
    outPtr drKey Frame hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc
    hsame

/-- `allocMemcpyVmSpec` convenience wrapper around `initializeBobSession_cut_full_placed_sat`. -/
public theorem initializeBobSession_cut_full_placed_std_sat [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {Qp : State → SepProp → Prop}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContractsSat M P C A lim H)
    (h_memcpy : HookSat H lsMemcpySym allocMemcpyVmSpec)
    (s0 : State) (st : M.σ) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
    (hfits : FitsEnv M lim st (AcceptOptFieldsEnv P inp))
    (hrun : s0.status = ExecStatus.Running)
    (hpc : s0.pc = (blkPl_75).base)
    (hsp_align : s0.spAligned = true)
    (h_3 : s0.readReg64 (.gpr 0#5) = argPtr)
    (h_4 : s0.readReg64 (.gpr 1#5) = ratchetKeyPairPtr)
    (h_5 : s0.readReg64 (.gpr 8#5) = outPtr)
    (h_6 : inp.trustedPeer = true) (h_7 : inp.replayOk = true)
    (h_8 : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (h_9 : WellSizedAcceptKeysInput inp)
    (h_10 : ikBPk.length = 32) (h_11 : spkBPk.length = 32)
    (hacc : acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool lim st s0 ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      Qp :=
  initializeBobSession_cut_full_placed_sat hWF hP hH
    (hookSat_framelessMemcpy_of_allocMemcpyVm h_memcpy)
    s0 st inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
    outPtr drKey Frame hfr hfits hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc
    hsame

end LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudgetSat
