/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptErrOwnedPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedB
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced

/-!
# `[LibsignalFullPlacement]` Corollaries for `Pqxdh::accept` and `initialize_bob_session`

Instantiates the `[LibsignalPlacement]` contracts for `Pqxdh::accept` (Block `79`) and
`initialize_bob_session` (Block `75`) with the shared canonical-key, signature-verification,
allocator/vector, and HKDF/agreement callee proofs under `[LibsignalFullPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.Shared
  (isCanonical_placed_ok'_cl vecAppendElements_fast_placed_ok_cl)

/-- Adapts `Shared.isCanonical_placed_ok'_cl` (`Block 202`) from `SignalPqxdh.Primitives` to
`CryptoGames.LibsignalSession.Primitives` (`ResponderCore.ecPubKeyIsCanonicalCallSpec P`) at
`lsmpl.base 202` under `[LibsignalFullPlacement]`. -/
theorem ecPubKeyIsCanonical_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hmontHook : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  obtain ⟨fnM, hfnM, hokM⟩ := hmontHook
  obtain ⟨fnT, hfnT, hokT⟩ := htorsHook
  exact (isCanonical_placed_ok'_cl (P := toSignalPqxdhPrimitives P)
    hWF.isCanonical_eq_isCanonicalRef hWF.montToEd_len
    ⟨fnM, hfnM, fun gm Rm sm hrunm hprem hspm =>
      hokM ⟨gm.inBytes, gm.signBit, gm.inPtr, gm.outPtr⟩ Rm sm hrunm hprem hspm⟩
    ⟨fnT, hfnT, fun gt Rt st hrunt hpret hspt =>
      hokT ⟨gt.inPtr, gt.inBytes⟩ Rt st hrunt hpret hspt⟩).mono_outcome
    ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp fun _ hout => hout

/-- Closed `[LibsignalFullPlacement]` contract for `Pqxdh::accept` (Block `79`) lifted to any
`callerProg` (`[IsLsBlockProg callerProg i H]`) at `lsmpl.base 79` from `PqxdhPlacedHookContracts`
and `HookSat H lsMemcpySym framelessMemcpySpec`. -/
theorem pqxdhAccept_opt_fields_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A) :=
  pqxdhAccept_opt_fields_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    (vecAppendElements_fast_placed_ok_cl h_memcpy)
    (hH.hkdfExtract_ok hP)
    (hH.hkdfExpandMultiInfo_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.kyberDecaps
    hH.handleError hH.handleAllocError

/-- Closed `[LibsignalFullPlacement]` owned-error rejecting contract for `Pqxdh::accept` (Block `79`)
lifted to any `callerProg` at `lsmpl.base 79`. -/
theorem pqxdhAccept_err_owned_full_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok callerProg (lsmpl.base 79)
      (pqxdhAcceptErrOwnedFrozenPlacedSpec P A) :=
  pqxdhAccept_err_owned_placed_ok_of_block hWF
    (ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
    (hH.calculateAgreement_ok hP)
    hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.handleError

/-- Closed `[LibsignalFullPlacement]` rejecting run of `initialize_bob_session` (Block `75`) on
`lsProg_75 H`. -/
theorem initializeBobSession_err_full_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrFrozenPlacedSpec P A) :=
  initializeBobSession_err_frozen_placed_ok_of_accept
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH h_memcpy)

/-- Closed `[LibsignalFullPlacement]` owned-error rejecting run of `initialize_bob_session`
(Block `75`) on `lsProg_75 H`. -/
theorem initializeBobSession_err_owned_full_placed_ok [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (lsProg_75 H) (blkPl_75).base
      (initializeBobSessionErrOwnedFrozenPlacedSpec P A) :=
  initializeBobSession_err_owned_frozen_placed_ok_of_accept
    (pqxdhAccept_err_owned_full_placed_ok_of_block hWF hP hH h_memcpy)

/-- Closed `[LibsignalFullPlacement]` frame-retaining cut of `initialize_bob_session` (Block `75`)
from entry to `spqr::initial_state` (`lsmpl.base 327`) for SPQR-V1 `BobTailV1`. -/
theorem initBob_to_spqr_full_placed [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk 0#8 ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (fun sf P_f =>
        (P_f ⊢
          bobSpqrCutCells s0.sp ratchetKeyPairPtr drKey.rootKey drKey.pqrKey drKey.chainKey
            spkBPk inp.spkBSk ∗
          bobFrameAtSpqr s0.sp drKey.rootKey drKey.pqrKey drKey.chainKey ∗
          (argPtr ↦ₛ bytesToBv8 ikBPk) ∗
          pqxdhAcceptOptFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr inp ∗
          ((argPtr + 297#64) ↦₈ 0#8) ∗
          memRegion outPtr 344 ∗ initBobSavedRegs s0.sp s0 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt (s0.sp - 768#64) pqxdhEntryStack ∗ A.pool ∗ Frame) ∧
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
      (BobPanicOom s0) :=
  initBob_to_spqr_full_frozen_placed_of_accept hWF
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH h_memcpy)
    s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc

/-- Closed `[LibsignalFullPlacement]` `BobCutPost` cut of `initialize_bob_session` (Block `75`) at
`spqr::initial_state` (`lsmpl.base 327`). -/
theorem initializeBobSession_cut_full_placed [LibsignalFullPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts P C A H)
    (h_memcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (s0 : State) (inp : AcceptKeysInput) (ikBPk spkBPk : Bytes) (sameAccountByte : BitVec 8)
    (argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr : BitVec 64)
    (drKey : DRKey) (Frame : SepProp)
    (hfr : LibsignalFrozen lsmpl s0.mem)
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
    (hacc : Model.acceptKeys P inp = some drKey) (hsame : sameAccountByte = 0#8) :
    SepWPp (lsProg_75 H) (lsmpl.base 327) s0
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr
        inp ikBPk spkBPk sameAccountByte ∗
       memRegion outPtr 344 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt s0.sp (768 + pqxdhEntryStack) ∗ A.pool ∗ Frame)
      (BobCutPost (blkPl_75).base s0 ratchetKeyPairPtr
        drKey.rootKey drKey.pqrKey drKey.chainKey spkBPk inp.spkBSk Frame)
      (BobPanicOom s0) :=
  initializeBobSession_cut_frozen_placed_of_accept hWF
    (pqxdhAccept_opt_fields_full_placed_ok_of_block hWF hP hH h_memcpy)
    s0 inp ikBPk spkBPk sameAccountByte argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hrun hpc hsp_align h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 hacc hsame

end CryptoVerification.E2E.Pqxdh.ResponderCore
