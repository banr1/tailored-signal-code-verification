/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainPhasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Master Composition for `PqRatchetState::encode_to_vec` (`Block 426`)

Defines the `.rodata`-explicit deterministic (`NoOom`) and envelope-based (`PqRatchetStateEncodeToVecEnv`)
specifications for `PqRatchetState::encode_to_vec` (`Block 426`), proves the end-to-end `SepWPp`
composition `pqRatchetStateEncodeToVec_gen_placed_ok`, and provides top-level `subroutine_ok` wrappers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
   extract_withLsCodeLoaded lsMemcpySym lsρ lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.LibsignalSpqrV1 (PqRatchetState V1State)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open CryptoVerification.SpqrV1.ProtoRepr
  (chunkedCt1SampledPBEncodedLen chunkedCt1SampledPBPinnedAt
   ct1SentPBEncodedLen ct1SentPBPinnedAt
   ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt
   polynomialDecoderPBEncodedLen polynomialDecoderPBPinnedAt
   polynomialEncoderPBEncodedLen polynomialEncoderPBPinnedAt
   v1StateJumpTableBytes v1StateJumpTableBytes_lsro_local2_intro v1StateJtSymLocal2)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStateEncodeToVecGhost PqRatchetStateEncodeToVecPinnedGhost
   StepInv blkPC_426 blkPl_426
   encodeToVecJumpTableBytes encodeToVecSavedRegs encodeToVecStackOf
   etvJumpTableBytes_lsro_intro etvJumpTableRoSym etv_sepWPp_mono_post
   pqRatchetStatePBAt pqRatchetStatePBAt_eq_exists_pinned
   pqRatchetStatePBEncodedLen pqRatchetStatePBEncodedLen_eq_proto pqRatchetStatePBPinnedAt
   withStepInv)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (chainEncodedLenPinnedSpec withLsRoLoaded)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentBudget
  (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
  (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext
   polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
  (ct1SentEncodedLen_local2_pinned_placed_ok_ext
   ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (encodeChainParamsSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBaseBudget
  (encodeEpochDirectionPinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ct1SentEncodePinnedSpecOf ekSentCt1ReceivedEncodePinnedSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExactBudget
  (encodePolyDecoderExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodePolyEncoderExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecEnv
   PqRatchetStateEncodeToVecPinnedPlacedOkExt PqRatchetStateEncodeToVecPlacedOkExt
   fitsEvents_pqRatchetStateEncodeToVec_of_fitsEnv
   pqRatchetStateEncodeToVecEnv_events pqRatchetStateEncodeToVecEvents
   pqRatchetStateEncodeToVecNoOomSpecOf pqRatchetStateEncodeToVecPinnedNoOomSpecOf
   pqRatchetStateEncodeToVecPinnedSpecOf pqRatchetStateEncodeToVecPinnedSpecX
   pqRatchetStateEncodeToVecSpecOf pqRatchetStateEncodeToVecSpecX)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (subroutine_ok_withStepInv_lscl withStepInvVm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeChainParamsExactSpecOf encodeEpochDirectionExactSpecOf
   encodeVarintExactSpecOf epochEncLenStackSpecOf etvMemcpyRegionSpec
   rustAllocStackSpecOf shimStackSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlacedBudget
  (step_encodeToVec_alloc_placed step_encodeToVec_epilogue_pool_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
  (etv_ct1SentEncode_of_spec etv_ekSentCt1ReceivedEncode_of_spec
   etv_encodeChainParams_exact_of_spec etv_encodeEpochDirection_exact_of_spec
   etv_polyDecoderEncode_budget_exact_of_spec etv_polyEncoderEncode_budget_exact_of_spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesPlacedBudget
  (etv_chainEncodedLen_placed_ok etv_encodeVarint_placed_ok etv_encodeVarint_placed_ok_x
   etv_epochEncodedLen_placed_ok etv_memcpy_placed_ok etv_rustAlloc_placed_ok
   etv_shim_placed_ok etv_subroutine_ok_placed_of_lscl etv_subroutine_ok_placed_of_plain
   etv_v1StateEncodedLen_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhasePlacedBudget
  (step_encodeToVec_phase1_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1ChainPhasePlacedBudget
  (step_encodeToVec_chain_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonBudget
  (leafEncLen16Spec leafEncLen48Spec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf etvEkSentCt1ReceivedBudgetExactSpecOf
   etvPolyDecoderBudgetExactSpecOf etvPolyEncoderBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhasePlacedBudget
  (step_encodeToVec_versionNeg_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

/-! ## 1. Re-Exports from `ProofPlacedBudgetAux` -/

abbrev v1StateEncodedLen_local2_pinned_placed_ok_hooks :=
  @ProofPlacedBudgetAux.v1StateEncodedLen_local2_pinned_placed_ok_hooks
abbrev v1StateEncodedLen_local2_placed_ok_hooks :=
  @ProofPlacedBudgetAux.v1StateEncodedLen_local2_placed_ok_hooks
abbrev v1StateEncodedLen_local2_pinned_placed_ok_ext :=
  @ProofPlacedBudgetAux.v1StateEncodedLen_local2_pinned_placed_ok_ext
abbrev v1StateEncodedLen_local2_placed_ok_ext :=
  @ProofPlacedBudgetAux.v1StateEncodedLen_local2_placed_ok_ext
abbrev v1StateEncodedLen_local2_pinned_placed_ok :=
  @ProofPlacedBudgetAux.v1StateEncodedLen_local2_pinned_placed_ok
abbrev v1StateEncodedLen_local2_placed_ok :=
  @ProofPlacedBudgetAux.v1StateEncodedLen_local2_placed_ok

abbrev StepInnerStateAt1880Placed :=
  @ProofPlacedBudgetAux.StepInnerStateAt1880Placed
abbrev step_encodeToVec_v1_ct1Sampled_at_1880_placed :=
  @ProofPlacedBudgetAux.step_encodeToVec_v1_ct1Sampled_at_1880_placed
abbrev step_encodeToVec_v1_ekSentCt1Received_at_1880_placed :=
  @ProofPlacedBudgetAux.step_encodeToVec_v1_ekSentCt1Received_at_1880_placed
abbrev step_encodeToVec_v1_ct1Acknowledged_at_1880_placed :=
  @ProofPlacedBudgetAux.step_encodeToVec_v1_ct1Acknowledged_at_1880_placed
abbrev step_encodeToVec_v1_ct1Received_at_1880_placed :=
  @ProofPlacedBudgetAux.step_encodeToVec_v1_ct1Received_at_1880_placed
abbrev step_encodeToVec_phase2d_placed :=
  @ProofPlacedBudgetAux.step_encodeToVec_phase2d_placed

/-! ## 2. `.rodata`-Explicit Budget Specifications (`Block 426`) -/

/-- `.rodata`-explicit deterministic (`NoOom`) pinned `Spec` of `PqRatchetState::encode_to_vec` (`Block 426`). -/
def pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf [LibsignalPlacement] (resStack : Nat)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecPinnedGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s0 =>
    ⌜s0.readReg64 .x0 = x.sret ∧
      s0.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEvents M lim st_a (pqRatchetStateEncodeToVecEvents x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool lim st_a s0 ∗
      stackAt s0.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool lim (M.stepEvents (pqRatchetStateEncodeToVecEvents x.st) st_a) sf ∗
      stackAt s0.sp (encodeToVecStackOf resStack)

/-- `.rodata`-explicit deterministic (`NoOom`) unpinned `Spec` of `PqRatchetState::encode_to_vec` (`Block 426`). -/
def pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf [LibsignalPlacement] (resStack : Nat)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s0 =>
    ⌜s0.readReg64 .x0 = x.sret ∧
      s0.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEvents M lim st_a (pqRatchetStateEncodeToVecEvents x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBAt A.repAlloc x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool lim st_a s0 ∗
      stackAt s0.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
      pqRatchetStatePBAt A.repAlloc x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool lim (M.stepEvents (pqRatchetStateEncodeToVecEvents x.st) st_a) sf ∗
      stackAt s0.sp (encodeToVecStackOf resStack)

/-- `.rodata`-explicit envelope-based pinned `Spec` of `PqRatchetState::encode_to_vec` (`Block 426`). -/
def pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf [LibsignalPlacement] (resStack : Nat)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecPinnedGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s0 =>
    ⌜s0.readReg64 .x0 = x.sret ∧
      s0.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEnv M lim st_a (PqRatchetStateEncodeToVecEnv x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool lim st_a s0 ∗
      stackAt s0.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PqRatchetStateEncodeToVecEnv x.st evs⌝ ∗
        vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
        (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
        ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
        A.pool lim (M.stepEvents evs st_a) sf ∗
        stackAt s0.sp (encodeToVecStackOf resStack)

/-- `.rodata`-explicit envelope-based unpinned `Spec` of `PqRatchetState::encode_to_vec` (`Block 426`). -/
def pqRatchetStateEncodeToVecRoPlacedSpecOf [LibsignalPlacement] (resStack : Nat)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PqRatchetStateEncodeToVecGhost × M.σ) where
  pre := fun ⟨x, st_a⟩ s0 =>
    ⌜s0.readReg64 .x0 = x.sret ∧
      s0.readReg64 .x1 = x.a ∧
      (PqRatchetState.encodeRaw x.st).length < 2 ^ 63 ∧
      FitsEnv M lim st_a (PqRatchetStateEncodeToVecEnv x.st)⌝ ∗
      memRegion x.sret 24 ∗
      pqRatchetStatePBAt A.repAlloc x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
      A.pool lim st_a s0 ∗
      stackAt s0.sp (encodeToVecStackOf resStack)
  post := fun ⟨x, st_a⟩ s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PqRatchetStateEncodeToVecEnv x.st evs⌝ ∗
        vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBAt A.repAlloc x.a x.st ∗
        (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
        ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
        A.pool lim (M.stepEvents evs st_a) sf ∗
        stackAt s0.sp (encodeToVecStackOf resStack)

/-! ## 3. Master End-to-End Composition (`Block 426`) -/

private theorem subroutine_ok_withStepInvVm_of_withStepInv {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} {s0 : State}
    (h : subroutine_ok prog entry (withStepInv s0 spec)) :
    subroutine_ok prog entry (withStepInvVm s0 spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      dsimp only [withStepInvVm, withStepInv] at hp ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨hp.1.1, hp.2⟩)
    (fun _ _ _ _ hq => hq)

/-- General end-to-end `SepWPp` execution of `PqRatchetState::encode_to_vec` (`Block 426`),
chaining Phase 1, Phase 2a, Phase 2b, Phase 2c, Phase 2d, and Epilogue. -/
theorem pqRatchetStateEncodeToVec_gen_placed_ok [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : PqRatchetStateEncodeToVecPinnedGhost} {st_a : M.σ} {R : SepProp} {s0 : State}
    (hChainLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 406)
      (withStepInv s0 (chainEncodedLenPinnedSpec A.repAlloc)))
    (hV1StateLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc (lsρ v1StateJtSymLocal2))))
    (hshim : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStepInv s0 (shimStackSpecOf resStack)))
    (halloc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (withStepInv s0 (rustAllocStackSpecOf resStack A lim)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "memcpy")
      etvMemcpyRegionSpec)
    (hcp_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 313)
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A lim)))
    (hep_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 399)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A.repAlloc)))
    (hed_call : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 317)
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A lim)))
    (hInnerAt1880 : ∀ (st1 : M.σ) (is : V1State.InnerState),
      StepInnerStateAt1880Placed resStack A lim st1 H s0 is)
    (hpc : s0.pc = (blkPl_426).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf resStack A lim).pre (x, st_a) s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) (s0.readReg64 .lr) s0 P
        (fun sf Q =>
          ((sf.mem ⊨ Q ∗ R) →
            StepInv s0 sf ∧
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf resStack A lim).post (x, st_a) s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf resStack A lim).onPanic (x, st_a) s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hpre_pure := hpre
  dsimp only [pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hlen_raw, hfits⟩, hpre_mem⟩ := hpre_pure
  have hlen : pqRatchetStatePBEncodedLen x.st < 2 ^ 63 := by
    rw [← pqRatchetStatePBEncodedLen_eq_proto x.st]; exact hlen_raw
  have hpre_rewritten : s0.mem ⊨
      ((pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
        (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
        stackAt s0.sp (encodeToVecStackOf resStack)) ∗
       (memRegion x.sret 24 ∗ ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes) ∗
        A.pool lim st_a s0)) ∗ R := by
    convert hpre_mem using 1; sep_ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  refine step_encodeToVec_phase1_placed hres A.repAlloc H (lsρ v1StateJtSymLocal2)
    (subroutine_ok_withStepInvVm_of_withStepInv hChainLen)
    (subroutine_ok_withStepInvVm_of_withStepInv hV1StateLen)
    x.sret x.a s0.sp x.g x.st hlen halign
    hpc hrun rfl hx0 hx1 rfl ?_
  intro s1 v0 v1 v2 v3 v4 v5 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1
  let st1 := M.stepEvents (pqRatchetStateEncodeToVecEvents x.st) st_a
  refine step_encodeToVec_alloc_placed A lim st_a H hshim halloc
    x.sret x.a s0.sp v0 v1 v2 v3 v4 v5 x.g x.st hlen hfits halign
    (F := memRegion x.sret 24 ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes))
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hfp1 hinv1.1
    (by rw [← A.pool_of_vmPreserved hinv1.2]; sep_ac_rfl) ?_
  intro s2 ptr hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2 hx27_2 hx28_2 hfp2 hinv2
  refine step_encodeToVec_versionNeg_placed A lim st1 H hvarint hmemcpy hcp_call
    x.sret x.a s0.sp ptr v0 v1 v2 x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes))
    hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2 hfp2 hinv2
    rfl ?_
  intro s3 w1 w2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
  refine step_encodeToVec_chain_placed hres A lim st1 H hChainLen hep_call hvarint hmemcpy hed_call hcp_call
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0 ∗ memRegion x.sret 24 ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes))
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx27_3 hx28_3 hfp3 hinv3
    (by sep_ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
  refine step_encodeToVec_phase2d_placed hres A lim st1 H (lsρ v1StateJtSymLocal2)
    hV1StateLen hvarint (hInnerAt1880 st1)
    x.sret x.a s0.sp ptr x.g x.st hlen halign
    (F := memRegion x.sret 24 ∗
      ((s0.sp - 144#64) ↦₆₄ v0) ∗ ((s0.sp - 136#64) ↦₆₄ w1) ∗ ((s0.sp - 128#64) ↦₆₄ w2) ∗
      encodeToVecSavedRegs s0.sp s0)
    hpc4 hrun4 hsp4 htr4 hx20_4 hx21_4 hx27_4 hx28_4 hfp4 hinv4
    (by sep_ac_rfl) ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx27_5 hfp5 hinv5
  refine step_encodeToVec_epilogue_pool_placed hres A lim st1 H
    x.sret s0.sp (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen x.st)) ptr v0 w1 w2
    (PqRatchetState.encodeRaw x.st)
    (F := pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
      (lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
      ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes))
    hpc5 hrun5 hsp5 halign htr5 hx27_5 hinv5
    (by sep_ac_rfl) ?_
  intro sf _ _ hspf htrf hcsf hinvf
  refine ⟨fun hm => ⟨hinvf, ?_⟩, hspf, hcsf⟩
  dsimp only [pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf, st1]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htrf, ?_⟩
  convert hm using 1; sep_ac_rfl

/-! ## 4. Unpinning & `NoOom` → `Env` Bridges -/

private theorem etv_sepWPp_mono_post_oom {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Q' Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s P Q Qp oom)
    (hQ : ∀ sf P_f, Q sf P_f → Q' sf P_f) :
    SepWPp prog ret s P Q' Qp oom := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | hpan | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hQ sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_noOom [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hno : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf resStack A lim)) :=
  subroutine_ok_mono hno
    (fun ⟨x, st_a⟩ _ R hp => by
      obtain ⟨hcl, hp⟩ := extract_withLsCodeLoaded hp
      dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf,
        pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf] at hp ⊢
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcl, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1,
        fitsEvents_pqRatchetStateEncodeToVec_of_fitsEnv M lim st_a x.st hp.1.2.2.2⟩, hp.2⟩)
    (fun ⟨x, st_a⟩ _ _ R hq => by
      dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf,
        pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨pqRatchetStateEncodeToVecEvents x.st,
        ⟨hq.1, pqRatchetStateEncodeToVecEnv_events x.st⟩,
        by simpa only [sepConj_assoc] using hq.2⟩)

theorem pqRatchetStateEncodeToVec_ro_noOom_placed_ok_of_pinned [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st_a⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.sret, x.a, g, x.st⟩, st_a) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoNoOomPlacedSpecOf]
    rw [pqRatchetStatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf resStack A lim))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st_a⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoPlacedSpecOf] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.sret, x.a, g, x.st⟩, st_a) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf,
      pqRatchetStateEncodeToVecRoPlacedSpecOf] at hpost ⊢
    simp only [pqRatchetStatePBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    exact ⟨evs, g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem pqRatchetStateEncodeToVec_pinned_placed_ok_of_noOom [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hno : subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecPinnedNoOomSpecOf resStack A lim)))) :
    subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecPinnedSpecOf resStack A lim))) :=
  subroutine_ok_mono hno
    (fun ⟨x, st_a⟩ s0 R hp => by
      dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecPinnedSpecOf,
        DefsBudget.pqRatchetStateEncodeToVecPinnedSpecOfEnv,
        pqRatchetStateEncodeToVecPinnedNoOomSpecOf] at hp ⊢
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have hp' := hp.2
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp' ⊢
      refine ⟨hp'.1, ?_⟩
      have hp'' := hp'.2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp'' ⊢
      exact ⟨⟨hp''.1.1, hp''.1.2.1, hp''.1.2.2.1,
        fitsEvents_pqRatchetStateEncodeToVec_of_fitsEnv M lim st_a x.st hp''.1.2.2.2⟩, hp''.2⟩)
    (fun ⟨x, st_a⟩ _ _ R hq => by
      dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecPinnedSpecOf,
        DefsBudget.pqRatchetStateEncodeToVecPinnedSpecOfEnv,
        pqRatchetStateEncodeToVecPinnedNoOomSpecOf] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨pqRatchetStateEncodeToVecEvents x.st,
        ⟨hq.1, pqRatchetStateEncodeToVecEnv_events x.st⟩,
        by simpa only [sepConj_assoc] using hq.2⟩)

theorem pqRatchetStateEncodeToVec_noOom_placed_ok_of_pinned [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecPinnedNoOomSpecOf resStack A lim)))) :
    subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecNoOomSpecOf resStack A lim))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st_a⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecNoOomSpecOf] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.sret, x.a, g, x.st⟩, st_a) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecNoOomSpecOf]
    rw [pqRatchetStatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem pqRatchetStateEncodeToVec_placed_ok_of_pinned [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hpinned : subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecPinnedSpecOf resStack A lim)))) :
    subroutine_ok prog entry
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecSpecOf resStack A lim))) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st_a⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecSpecOf,
    DefsBudget.pqRatchetStateEncodeToVecSpecOfEnv] at hpre
  rw [pqRatchetStatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome (⟨x.sret, x.a, g, x.st⟩, st_a) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecPinnedSpecOf,
      pqRatchetStateEncodeToVecSpecOf, DefsBudget.pqRatchetStateEncodeToVecPinnedSpecOfEnv,
      DefsBudget.pqRatchetStateEncodeToVecSpecOfEnv] at hpost ⊢
    simp only [pqRatchetStatePBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    exact ⟨evs, g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-! ## 5. Top-Level `subroutine_ok` Wrappers (`doReserveStack` and `doReserveStackX`) -/

/-- Top-level `NoOom` `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf doReserveStack A lim)`. -/
theorem pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf doReserveStack A lim)) := by
  apply subroutine_ok_of_sepWPp; intro ⟨x, st_a⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hvarint := etv_encodeVarint_placed_ok h_panic hshim halloc hrealloc s0 hcl0
  have hcp_call := subroutine_ok_withStepInv_lscl hcl0 hcp_ok
  have hep_call := etv_epochEncodedLen_placed_ok (resStack := doReserveStack) (by decide) A.repAlloc ext s0 hcl0
  have hed_call := subroutine_ok_withStepInv_lscl hcl0 hed_ok
  have hpolyEnc := subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok
  have hpolyDec := subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok
  have hekEnc := subroutine_ok_withStepInv_lscl hcl0 hekEnc_ok
  have hct1SentEnc := subroutine_ok_withStepInv_lscl hcl0 hct1SentEnc_ok
  have hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 407)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A.repAlloc) chunkedCt1SampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hInnerAt1880 : ∀ (st1 : M.σ) (is : V1State.InnerState),
      StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 is := by
    intro st1 is; cases is with
    | keysUnsampled v => exact hKeysUnsampled s0 st1 hcl0 v
    | keysSampled v => exact hKeysSampled s0 st1 hcl0 v
    | headerSent v => exact hHeaderSent s0 st1 hcl0 v
    | ct1Received v =>
      exact step_encodeToVec_v1_ct1Received_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
    | ekSentCt1Received v =>
      exact step_encodeToVec_v1_ekSentCt1Received_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hekLen hpolyDecLen hvarint hekEnc hpolyDec v
    | noHeaderReceived v => exact hNoHeaderReceived s0 st1 hcl0 v
    | headerReceived v => exact hHeaderReceived s0 st1 hcl0 v
    | ct1Sampled v =>
      exact step_encodeToVec_v1_ct1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
    | ekReceivedCt1Sampled v => exact hEkReceivedCt1Sampled s0 st1 hcl0 v
    | ct1Acknowledged v =>
      exact step_encodeToVec_v1_ct1Acknowledged_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
    | ct2Sampled v => exact hCt2Sampled s0 st1 hcl0 v
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_placed_ok (by decide)
    (etv_chainEncodedLen_placed_ok A.repAlloc ext s0 hcl0)
    (etv_v1StateEncodedLen_placed_ok A.repAlloc ext s0 hcl0
      (v1StateEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
    (etv_shim_placed_ok hshim s0)
    (etv_rustAlloc_placed_ok (by decide) (by decide) halloc s0)
    hvarint
    (etv_memcpy_placed_ok hmc)
    hcp_call hep_call hed_call hInnerAt1880
    hpc hrun hpre hsp
  exact ⟨P, R, hP,
    etv_sepWPp_mono_post_oom hwp (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => (hq hm).2, hspf, hcsf⟩)⟩

theorem pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPinnedPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_noOom
    (pqRatchetStateEncodeToVec_ro_pinned_noOom_placed_ok_of_variants
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

theorem pqRatchetStateEncodeToVec_ro_placed_ok_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStack A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStack A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStack A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStack A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecRoPlacedSpecOf doReserveStack A lim)) :=
  pqRatchetStateEncodeToVec_ro_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_ro_pinned_placed_ok_of_variants
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

/-- Top-level `NoOom` `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) on
`withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl (pqRatchetStateEncodeToVecPinnedNoOomSpecOf doReserveStackX A lim))`,
eliminating both `.rodata` jump-table atoms via `LibsignalRoLoaded lsmpl`. -/
theorem pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecPinnedNoOomSpecOf doReserveStackX A lim))) := by
  apply subroutine_ok_of_sepWPp; intro ⟨x, st_a⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hro0, hpre⟩ := hpre
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have hpre_ro1 := v1StateJumpTableBytes_lsro_local2_intro hro0 hpre
  have hpre_ro2 := etvJumpTableBytes_lsro_intro hro0 hpre_ro1
  have hpre_ro : s0.mem ⊨
      (pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf doReserveStackX A lim).pre (x, st_a) s0 ∗ R := by
    dsimp only [pqRatchetStateEncodeToVecPinnedNoOomSpecOf,
      pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf, lsρ] at hpre_ro2 ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre_ro2
  have hvarint := etv_encodeVarint_placed_ok_x h_panic hshim halloc hrealloc s0 hcl0
  have hcp_call := subroutine_ok_withStepInv_lscl hcl0 hcp_ok
  have hep_call := etv_epochEncodedLen_placed_ok (resStack := doReserveStackX) (by decide) A.repAlloc ext s0 hcl0
  have hed_call := subroutine_ok_withStepInv_lscl hcl0 hed_ok
  have hpolyEnc := subroutine_ok_withStepInv_lscl hcl0 hpolyEnc_ok
  have hpolyDec := subroutine_ok_withStepInv_lscl hcl0 hpolyDec_ok
  have hekEnc := subroutine_ok_withStepInv_lscl hcl0 hekEnc_ok
  have hct1SentEnc := subroutine_ok_withStepInv_lscl hcl0 hct1SentEnc_ok
  have hct1SampledLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 407)
      (withStepInv s0 (leafEncLen48Spec (chunkedCt1SampledPBPinnedAt A.repAlloc) chunkedCt1SampledPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_lscl hcl0
      (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hekLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 421)
      (withStepInv s0 (leafEncLen16Spec (ekSentCt1ReceivedPBPinnedAt A.repAlloc) ekSentCt1ReceivedPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ekSentCt1ReceivedEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hpolyDecLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 413)
      (withStepInv s0 (leafEncLen16Spec (polynomialDecoderPBPinnedAt A.repAlloc) polynomialDecoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hct1SentLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 408)
      (withStepInv s0 (leafEncLen16Spec (ct1SentPBPinnedAt A.repAlloc) ct1SentPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (ct1SentEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hpolyEncLen : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 401)
      (withStepInv s0 (leafEncLen16Spec (polynomialEncoderPBPinnedAt A.repAlloc) polynomialEncoderPBEncodedLen)) :=
    etv_subroutine_ok_placed_of_plain hcl0
      (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext)
  have hInnerAt1880 : ∀ (st1 : M.σ) (is : V1State.InnerState),
      StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 is := by
    intro st1 is; cases is with
    | keysUnsampled v => exact hKeysUnsampled s0 st1 hcl0 v
    | keysSampled v => exact hKeysSampled s0 st1 hcl0 v
    | headerSent v => exact hHeaderSent s0 st1 hcl0 v
    | ct1Received v =>
      exact step_encodeToVec_v1_ct1Received_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hekLen hpolyEncLen hvarint hekEnc hpolyEnc v
    | ekSentCt1Received v =>
      exact step_encodeToVec_v1_ekSentCt1Received_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hekLen hpolyDecLen hvarint hekEnc hpolyDec v
    | noHeaderReceived v => exact hNoHeaderReceived s0 st1 hcl0 v
    | headerReceived v => exact hHeaderReceived s0 st1 hcl0 v
    | ct1Sampled v =>
      exact step_encodeToVec_v1_ct1Sampled_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hct1SampledLen hvarint hct1SentEnc hpolyEnc hpolyDec v
    | ekReceivedCt1Sampled v => exact hEkReceivedCt1Sampled s0 st1 hcl0 v
    | ct1Acknowledged v =>
      exact step_encodeToVec_v1_ct1Acknowledged_at_1880_placed (by decide) A lim st1 (Rust.withPanics ext)
        hct1SentLen hpolyDecLen hvarint hct1SentEnc hpolyDec v
    | ct2Sampled v => exact hCt2Sampled s0 st1 hcl0 v
  obtain ⟨P, hP, hwp⟩ := pqRatchetStateEncodeToVec_gen_placed_ok (by decide)
    (etv_chainEncodedLen_placed_ok A.repAlloc ext s0 hcl0)
    (etv_v1StateEncodedLen_placed_ok A.repAlloc ext s0 hcl0
      (v1StateEncodedLen_local2_pinned_placed_ok_ext A.repAlloc ext))
    (etv_shim_placed_ok hshim s0)
    (etv_rustAlloc_placed_ok (by decide) (by decide) halloc s0)
    hvarint
    (etv_memcpy_placed_ok hmc)
    hcp_call hep_call hed_call hInnerAt1880
    hpc hrun hpre_ro hsp
  refine ⟨P, R, hP, etv_sepWPp_mono_post_oom hwp (fun sf Q ⟨hq, hspf, hcsf⟩ => ⟨fun hm => ?_, hspf, hcsf⟩)⟩
  obtain ⟨_, hpost_ro⟩ := hq hm
  dsimp only [withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecRoPinnedNoOomPlacedSpecOf,
    pqRatchetStateEncodeToVecPinnedNoOomSpecOf] at hpost_ro ⊢
  have hpost_perm : sf.mem ⊨
      ((lsρ v1StateJtSymLocal2 ↦ᵣ v1StateJumpTableBytes) ∗
       ((blkPl_426).ρ etvJumpTableRoSym ↦ᵣ encodeToVecJumpTableBytes)) ∗
      ((⌜sf.trace = s0.trace⌝ ∗
        vecU8 A.repAlloc x.sret (PqRatchetState.encodeRaw x.st) ∗
        pqRatchetStatePBPinnedAt A.repAlloc x.g x.a x.st ∗
        A.pool lim (M.stepEvents (pqRatchetStateEncodeToVecEvents x.st) st_a) sf ∗
        stackAt s0.sp (encodeToVecStackOf doReserveStackX)) ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_ro
  exact Satisfies.of_sep_right hpost_perm

theorem pqRatchetStateEncodeToVec_noOom_placed_ok_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
      (blkPl_426).base
      (withLsRoLoaded lsmpl (withLsCodeLoaded lsmpl
        (pqRatchetStateEncodeToVecNoOomSpecOf doReserveStackX A lim))) :=
  pqRatchetStateEncodeToVec_noOom_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_variants
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) discharging
`PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext`. -/
theorem pqRatchetStateEncodeToVec_pinned_placed_ok_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_pinned_placed_ok_of_noOom
    (pqRatchetStateEncodeToVec_pinned_noOom_placed_ok_of_variants
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

/-- Top-level `subroutine_ok` for `PqRatchetState::encode_to_vec` (`Block 426`) discharging
`PqRatchetStateEncodeToVecPlacedOkExt A lim ext`. -/
theorem pqRatchetStateEncodeToVec_placed_ok_of_variants [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionExactSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (etvPolyEncoderBudgetExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (etvPolyDecoderBudgetExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    PqRatchetStateEncodeToVecPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_of_variants
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

/-! ## 6. Convenience Wrappers Accepting Callee Contracts Directly -/

private theorem lift_withLsCodeLoaded_bridge [LibsignalPlacement] {α β : Type} {prog : Program} {entry : BitVec 64}
    {spec1 : Spec α} {spec2 : Spec β}
    (hbr : ∀ s0 : State, subroutine_ok prog entry (withStepInv s0 spec1) →
      subroutine_ok prog entry (withStepInv s0 spec2))
    (hok : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec1)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec2) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  have h1 : subroutine_ok prog entry (withStepInv s0 spec1) :=
    subroutine_ok_withStepInv_lscl hcl0 hok
  have h2 := hbr s0 h1
  have hpre2 : s0.mem ⊨ (withStepInv s0 spec2).pre x s0 ∗ R := by
    dsimp only [withStepInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨StepInv.refl s0, hpre⟩
  exact h2.mono_outcome x R s0 hpc hrun hpre2 hsp fun _ hout => hout

theorem pqRatchetStateEncodeToVec_pinned_placed_ok_of_raw_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOf doReserveStackX A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    PqRatchetStateEncodeToVecPinnedPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_pinned_placed_ok_of_variants
    h_panic hshim halloc hrealloc hmc
    (lift_withLsCodeLoaded_bridge (fun _ => etv_encodeChainParams_exact_of_spec (resStack := doReserveStackX) (by decide)) hcp_ok)
    (lift_withLsCodeLoaded_bridge (fun _ => etv_encodeEpochDirection_exact_of_spec (resStack := doReserveStackX) (by decide)) hed_ok)
    (lift_withLsCodeLoaded_bridge (fun _ => etv_polyEncoderEncode_budget_exact_of_spec) hpolyEnc_ok)
    (lift_withLsCodeLoaded_bridge (fun _ => etv_polyDecoderEncode_budget_exact_of_spec) hpolyDec_ok)
    (lift_withLsCodeLoaded_bridge (fun _ => etv_ekSentCt1ReceivedEncode_of_spec) hekEnc_ok)
    (lift_withLsCodeLoaded_bridge (fun _ => etv_ct1SentEncode_of_spec) hct1SentEnc_ok)
    hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
    hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled

theorem pqRatchetStateEncodeToVec_placed_ok_of_raw_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hcp_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 313)
      (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf doReserveStackX A lim)))
    (hed_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 317)
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf doReserveStackX A lim)))
    (hpolyEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 316)
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A lim)))
    (hpolyDec_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 315)
      (withLsCodeLoaded lsmpl (encodePolyDecoderExactSpecOf doReserveStackX A lim)))
    (hekEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 318)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOf doReserveStackX A lim)))
    (hct1SentEnc_ok : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext)) (lsmpl.base 319)
      (withLsCodeLoaded lsmpl (ct1SentEncodePinnedSpecOf doReserveStackX A lim)))
    (hKeysUnsampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysUnsampled v))
    (hKeysSampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.keysSampled v))
    (hHeaderSent : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerSent v))
    (hNoHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.noHeaderReceived v))
    (hHeaderReceived : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.headerReceived v))
    (hEkReceivedCt1Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ekReceivedCt1Sampled v))
    (hCt2Sampled : ∀ (s0 : State) (st1 : M.σ), LibsignalCodeLoaded lsmpl s0.mem →
      ∀ v, StepInnerStateAt1880Placed doReserveStackX A lim st1 (Rust.withPanics ext) s0 (.ct2Sampled v)) :
    PqRatchetStateEncodeToVecPlacedOkExt A lim ext :=
  pqRatchetStateEncodeToVec_placed_ok_of_pinned
    (pqRatchetStateEncodeToVec_pinned_placed_ok_of_raw_callees
      h_panic hshim halloc hrealloc hmc
      hcp_ok hed_ok hpolyEnc_ok hpolyDec_ok hekEnc_ok hct1SentEnc_ok
      hKeysUnsampled hKeysSampled hHeaderSent hNoHeaderReceived
      hHeaderReceived hEkReceivedCt1Sampled hCt2Sampled)

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.ProofPlacedBudget
