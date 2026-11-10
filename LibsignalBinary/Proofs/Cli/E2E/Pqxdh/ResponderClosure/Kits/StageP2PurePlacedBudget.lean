/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees

/-!
# Budget-Threaded Relocatable Stage P2 Pure and Internal Callee Instantiation

Lifts `RustCliAllocBudget M` / `VmPreserved` internal callees, drop glue, and Block `75`
(`initialize_bob_session`) specs to `stageP1ProgPlaced ext`, defining `InitializeBobV1OptFieldsEnv`
and constructing `StageP2PureCalleesPlaced*` and `StageP2BaseCalleesPlaced4K`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalFrozen LibsignalFullPlacement LibsignalHooks
  LibsignalPlacement
  blkLib_eq_47 blkLib_eq_50 blkLib_eq_51 blkLib_eq_83
  blkPC_47 blkPC_50 blkPC_51 blkPC_70 blkPC_75 blkPC_83 blkPC_113 blkPC_252
  blkPl_47 blkPl_50 blkPl_51 blkPl_70 blkPl_75 blkPl_83 blkPl_113 blkPl_252
  libsignalMutatedBlocks libsignalSessionLib
  lsBlackBoxU8Sym ls_externAt?_blockProgram_eq_of_externs_eq ls_hook_ok_of_mem
  ls_subroutine_ok_cl_of_plain ls_subroutine_ok_of_block
  lsLogFilterAddr lsMemcpySym lsProg_75 lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (uuidTryParseCodeSpec withLsCodeRoLoaded withLsFrozen)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet.Getters (withLsRoLoaded)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded ls_subroutine_ok_rocl_of_block speWordsAt
  subroutine_ok_withLsCodeRoLoaded_of_rocl
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput Bytes DRKey Primitives StructuralPrims WellSizedAcceptKeysInput
  bytesToBv8 encodeEC pqxdhEntryStack pqxdhEntryStackExt
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  InitBobCallGhost PrimitivesMatchCrypto bobParamsFieldsAt initBobErrAt initBobErrAt_merge
  initBobErrOwnedAt ls_subroutine_ok_withLsFrozen_of_block pqxdhAcceptErrPayloadAt
)
open CryptoVerification.E2E.Pqxdh.ResponderStore (
  archiveCurrentStateInnerEmptySpec bv_sub_add_lit' mapIterNextEmptySpec
  pointsTo64_memRegion_336_entails_344 sessionRecordEmptyHeaderAt stackAt_split_top
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (stageP2bStack)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost initialStateValue)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2BobSession344Bv8V1 p2BobSpqrParams p2_stackAt_split_of_le stageP1ProgPlaced
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  PoolPreserved RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved
  fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
  rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec framelessMemcpySpec noAllocShimBudgetSpec publicKeySerializeSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  KemKeyPairFromPubPrivEnv curveKeyPairSerdeBudgetSpec curveKeyPairSerde_placed_ok
  kemKeyPairFromPubPrivEvents kemKeyPairFromPubPrivOkSpec kemKeyPairSerde_placed_ok
  preKeyRecordKeyPairBudgetSpec preKeyRecordKeyPair_placed_ok
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget (drop_spe2_placed_ok_at)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget (
  isSameAccountEqDistinct_placed_ok_at
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (
  pqxdhAcceptOptFieldsFrozenPlacedSpec pqxdhAcceptOptFieldsPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  PqxdhPlacedHookContracts
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (
  AcceptOptFieldsEnv acceptOptFieldsEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobPlacedBudget (
  InitBobSessionBuildEnv initBobSessionBuildEvents initializeBobSessionInnerPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (
  AcceptSuccessEnv initializeBobSessionErrFrozenPlacedSpec initializeBobSessionErrInnerPlacedSpec
  initializeBobSessionErrPlacedSpec initializeBobSession_err_placed_ok_of_accept
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSessionErrOwnedFrozenPlacedSpec initializeBobSessionErrOwnedInnerPlacedSpec
  initializeBobSessionErrOwnedPlacedSpec initializeBobSession_err_owned_placed_ok_of_accept
  pqxdhAcceptErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollariesBudget (
  initializeBobSession_err_full_placed_ok initializeBobSession_err_full_placed_ok_std
  initializeBobSession_err_owned_full_placed_ok initializeBobSession_err_owned_full_placed_ok_std
)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget (
  InitBobV1EnvOfEnv InitialStateMemInvPlacedOk InitialStateMemInvPlacedOkOfEnv
  bobSpqrGhost hookSat_sessionShimBudget_of_noAllocShimBudget
  initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded initialStateFrozenPlacedOk_of_codeRoLoaded
  initializeBobSession_ok_v1_frozen_placed_of_accept_of_session
  initializeBobSession_ok_v1_full_placed_of_env_of_session
  initializeBobSession_ok_v1_full_placed_of_env_std
  initializeBobSession_ok_v1_placed_of_accept_of_session
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_ok_at
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  isSameAccountDistinctSpec isSameAccountDistinctSpecExt p2BobSpqrVecBufBudget
  p2Memcpy4KSpec promoteStateEmpty4KSpec promoteStateEmptySpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  BobSpqrInitialStateEnv InitializeBobV1Env
  InitializeBobV1FrozenOkAtPlaced InitializeBobV1FrozenOkAtPlacedOfEnv
  InitializeBobV1FrozenOkPlaced InitializeBobV1FrozenOkPlaced4K
  InitializeBobV1FrozenOkPlaced4KOfEnv InitializeBobV1FrozenOkPlacedOfEnv
  InitializeBobV1MemInvOkAtPlaced InitializeBobV1MemInvOkAtPlacedOfEnv
  InitializeBobV1MemInvOkPlaced InitializeBobV1MemInvOkPlaced4K
  InitializeBobV1MemInvOkPlaced4KOfEnv InitializeBobV1MemInvOkPlacedOfEnv
  InitializeBobV1OkAtPlaced InitializeBobV1OkAtPlacedOfEnv
  InitializeBobV1OkPlaced InitializeBobV1OkPlacedOfEnv
  InitializeBobV1OkPlaced4K InitializeBobV1OkPlaced4KOfEnv
  StageP2BaseCalleesPlaced4K
  StageP2PureCalleesPlaced StageP2PureCalleesPlacedOfEnv
  StageP2PureCalleesPlaced4K StageP2PureCalleesPlaced4KOfEnv
  dropProcessPrekeyImplState1Spec
  initializeBobSessionErr4KInnerPlacedSpec initializeBobSessionErr4KPlacedSpec
  initializeBobSessionErrFrozen4KPlacedSpec
  initializeBobSessionErrOwned4KInnerPlacedSpec initializeBobSessionErrOwned4KPlacedSpec
  initializeBobSessionErrOwnedPlacedSpec_to_4K initializeBobSessionErrPlacedSpec_to_4K
  p2_publicKeySerialize_of_hooks_placed promoteMatchingSessionEmptySpec withBobMemInv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  of_stageP2Defs_errOwned4K_frozen_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  isSameAccountDistinctSpec_lscl_to_ext promoteStateEmptySpec_lscl_to_4K
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlacedBudget (
  drop_process_prekey_impl_state1_ext_placed_ok
)

/-! ## 1. `TrapsOnly` Extern-Table Refinement Lifting & `InitializeBobV1OptFieldsEnv` -/

theorem initializeBobV1OkAtPlacedOfEnv_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext1 bobV1Stk) :
    InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext2 bobV1Stk :=
  InitializeBobV1OkAtPlacedOfEnv.of_trapsOnly hT h

theorem initializeBobV1OkAtPlaced_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkAtPlaced P A lim F ext1 bobV1Stk) :
    InitializeBobV1OkAtPlaced P A lim F ext2 bobV1Stk :=
  InitializeBobV1OkAtPlacedOfEnv.of_trapsOnly hT h

theorem initializeBobV1OkPlaced_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkPlaced P A lim F ext1) :
    InitializeBobV1OkPlaced P A lim F ext2 :=
  InitializeBobV1OkPlacedOfEnv.of_trapsOnly hT h

theorem initializeBobV1OkPlaced4K_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1OkPlaced4K P A lim F ext1) :
    InitializeBobV1OkPlaced4K P A lim F ext2 :=
  InitializeBobV1OkPlaced4KOfEnv.of_trapsOnly hT h

theorem stageP2PureCalleesPlaced_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2PureCalleesPlaced P A lim F AcceptErrEnv ext1) :
    StageP2PureCalleesPlaced P A lim F AcceptErrEnv ext2 :=
  StageP2PureCalleesPlacedOfEnv.of_trapsOnly hT h

theorem stageP2PureCalleesPlaced4K_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext1) :
    StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext2 :=
  StageP2PureCalleesPlaced4KOfEnv.of_trapsOnly hT h

/-- Sequential allocator event envelope for SPQR V1 `initialize_bob_session` (`Block 75`) paired
with Block `79`'s full `AcceptOptFieldsEnv P inp` (`acceptOptFieldsEvents P inp`),
`BobSpqrInitialStateEnv F drKey.pqrKey`, and `InitBobSessionBuildEnv`. -/
def InitializeBobV1OptFieldsEnv (P : Primitives) (F : ShaCompress)
    (inp : AcceptKeysInput) (drKey : DRKey) : List AllocEvent → Prop :=
  SeqEnv (AcceptOptFieldsEnv P inp)
    (SeqEnv (BobSpqrInitialStateEnv F drKey.pqrKey) InitBobSessionBuildEnv)

theorem initializeBobV1OptFieldsEnv_of_parts {P : Primitives} {F : ShaCompress}
    {inp : AcceptKeysInput} {drKey : DRKey} {evs1 evs2 evs3 : List AllocEvent}
    (h1 : AcceptOptFieldsEnv P inp evs1)
    (h2 : BobSpqrInitialStateEnv F drKey.pqrKey evs2)
    (h3 : InitBobSessionBuildEnv evs3) :
    InitializeBobV1OptFieldsEnv P F inp drKey (evs1 ++ evs2 ++ evs3) := by
  rw [List.append_assoc]
  exact SeqEnv.append h1 (SeqEnv.append h2 h3)

-- Concrete inhabitation witness for `InitializeBobV1OptFieldsEnv P F inp drKey`.
example (P : Primitives) (F : ShaCompress) (inp : AcceptKeysInput) (drKey : DRKey) :
    InitializeBobV1OptFieldsEnv P F inp drKey
      (acceptOptFieldsEvents P inp ++ initBobSessionBuildEvents) := by
  simpa using initializeBobV1OptFieldsEnv_of_parts (P := P) (F := F) (inp := inp) (drKey := drKey)
    (evs1 := acceptOptFieldsEvents P inp) (evs2 := []) (evs3 := initBobSessionBuildEvents)
    rfl (SpqrBoundedEvs.nil _ _) rfl

/-! ## 2. Block-Lifted Pure & Hook-Backed Internal Callees (`stageP1ProgPlaced ext`) -/

section PlacedPureAnd4KCallees

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero

local macro "cells_unfold_fast" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub])

private theorem p2_cells_sub32_4_merge_placed (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

private theorem p2_stackAt_kemKeyPairFromPubPriv_placed (sp : BitVec 64) :
    memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  have h1 := stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 := ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)
  have h3 : (64 + allocHookStack : Nat) = allocHookStack + 8 * 8 := by decide
  have h4 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

private theorem p2_stackAt_promote_state_split_placed (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 4000 ∗ cells (sp - 96#64) 8 ∗ cells (sp - 32#64) 4 := by
  dsimp only [stackAt, allocHookStack]
  rw [show (4096 : Nat) = 4000 + (64 + 32) by decide,
    memRegion_split (sp - 4096#64) 4000 (64 + 32) (by decide),
    show sp - 4096#64 + 4000#64 = sp - 96#64 by bv_omega,
    memRegion_split (sp - 96#64) 64 32 (by decide),
    show sp - 96#64 + 64#64 = sp - 32#64 by bv_omega,
    ProofLib.memRegion_cells (sp - 96#64) 8 (by decide),
    ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]

/-- `VmPreserved`-strengthened `<Map<Iter<Vec<u8>>, ...> as Iterator>::next` (`Block 83`,
empty-slice fast path). -/
theorem map_iter_next_empty_vm_placed_ok [LibsignalPlacement] (ext : LibsignalHooks) :
    subroutine_ok ((blkPC_83).rebase (blkPl_83).base ext) (blkPl_83).base
      (withVmPreserved mapIterNextEmptySpec) := by
  dsimp only [withVmPreserved, mapIterNextEmptySpec]
  cells_unfold
  wp_init x s0
  obtain ⟨outPtr, iterPtr, slicePtr⟩ := x
  dsimp only at *
  subst h h_1
  wp_pull_exists
  apply sepWP_seg_ls_vm (Q := (blkPC_83).rebase (blkPl_83).base (hooksException ext))
    blkLib_eq_83 (mid := s0.readReg64 (.gpr 30#5))
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm_f : VmPreserved s0 _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [wp_norm, arm64_norm] at hvm_f
  wp_done

/-- `VmPreserved`-strengthened `SessionRecord::promote_matching_session` (`Block 50`,
empty-record fast path). -/
theorem promote_matching_session_empty_placed_ok [LibsignalPlacement] (ext : LibsignalHooks) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base ext) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec) := by
  dsimp only [promoteMatchingSessionEmptySpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderStore.promoteMatchingSessionEmptySpec,
    sessionRecordEmptyHeaderAt]
  cells_unfold_fast
  wp_init x s0
  obtain ⟨recPtr, outPtr⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_1 h_2
  have hiter := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_50).rebase (blkPl_50).base ext) (entry := lsmpl.base 83)
    (map_iter_next_empty_vm_placed_ok ext)
  simp only [withLsCl, withVmPreserved, mapIterNextEmptySpec, cells,
    sepExists_sepConj_right, sepConj_emp] at hiter
  wp_pull_exists
  apply SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk) h (mid := lsmpl.base 83)
  apply sepWP_seg_ls_vm (Q := (blkPC_50).rebase (blkPl_50).base (hooksException ext))
    blkLib_eq_50 (mid := lsmpl.base 83)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
  wp_call hiter (s0.sp - 448#64, s0.sp - 1128#64, 8#64)
  have hvm2 : VmPreserved s0 sf := hvm1.trans ‹_›
  clear hvm1
  apply sepWP_seg_ls_vm (Q := (blkPC_50).rebase (blkPl_50).base (hooksException ext))
    blkLib_eq_50 (mid := s0.readReg64 (.gpr 30#5))
  intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm_f : VmPreserved s0 _ :=
    hvm2.trans (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  simp only [wp_norm, arm64_norm] at hvm_f
  wp_done

/-- `SessionRecord::promote_matching_session` (`lsmpl.base 50`) on `stageP1ProgPlaced ext`. -/
theorem promote_matching_session_empty_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)} :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 50)
      (withLsCodeLoaded lsmpl promoteMatchingSessionEmptySpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 50)
    (promote_matching_session_empty_placed_ok ext) (by decide)

/-- `<curve::KeyPair as KeyPairSerde>::from_public_and_private` (`lsmpl.base 112`) on
`stageP1ProgPlaced ext`. -/
theorem curveKeyPairSerde_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)} :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 112)
      (withLsCodeLoaded lsmpl curveKeyPairSerdeBudgetSpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 112)
    (curveKeyPairSerde_placed_ok ext) (by decide)

/-- `<PreKeyRecord>::key_pair` (`lsmpl.base 67`) on `stageP1ProgPlaced ext`. -/
theorem preKeyRecordKeyPair_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)} :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 67)
      (withLsCodeLoaded lsmpl preKeyRecordKeyPairBudgetSpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 67)
    (preKeyRecordKeyPair_placed_ok ext) (by decide)

/-- `VmPreserved`-strengthened `<SessionRecord>::archive_current_state_inner` (`Block 51`,
empty-session fast path). -/
theorem archive_current_state_inner_empty_vm_placed_ok [LibsignalPlacement]
    (ext : LibsignalHooks) :
    subroutine_ok ((blkPC_51).rebase (blkPl_51).base ext) (blkPl_51).base
      (withVmPreserved archiveCurrentStateInnerEmptySpec) := by
  dsimp only [withVmPreserved, archiveCurrentStateInnerEmptySpec]
  cells_unfold
  wp_init recPtr s0
  subst h
  wp_pull_exists
  apply sepWP_seg_ls_vm (Q := (blkPC_51).rebase (blkPl_51).base (hooksException ext))
    blkLib_eq_51 (mid := s0.readReg64 (.gpr 30#5))
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm_f : VmPreserved s0 _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  simp only [wp_norm, arm64_norm] at hvm_f
  wp_done

/-- `VmPreserved`-strengthened `SessionRecord::promote_state` (`Block 47`, 0-stack
`framelessMemcpyBudgetSpec`). -/
theorem promote_state_empty_placed_ok [LibsignalPlacement] (ext : LibsignalHooks)
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok ((blkPC_47).rebase (blkPl_47).base ext) (blkPl_47).base
      (withLsCodeLoaded lsmpl promoteStateEmptySpec) := by
  dsimp only [promoteStateEmptySpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderStore.promoteStateEmptySpec]
  wp_init x s0
  obtain ⟨recPtr, srcPtr, bs⟩ := x
  dsimp only [withLsCodeLoaded] at *
  subst h_2 h_3
  have harch := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_47).rebase (blkPl_47).base ext) (entry := lsmpl.base 51)
    (archive_current_state_inner_empty_vm_placed_ok ext)
  simp only [withLsCl, withVmPreserved, archiveCurrentStateInnerEmptySpec] at harch
  have hmc : subroutine_ok ((blkPC_47).rebase (blkPl_47).base ext)
      (lsρ lsMemcpySym) framelessMemcpyBudgetSpec :=
    ls_hook_ok_of_mem hMemcpy
  dsimp only [framelessMemcpyBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hmc
  have hc4 : cells (s0.sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
        ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [hc4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  apply SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk) h (mid := lsmpl.base 51)
  apply sepWP_seg_ls_vm (Q := (blkPC_47).rebase (blkPl_47).base (hooksException ext))
    blkLib_eq_47 (mid := lsmpl.base 51)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
  have hsp_sub : s0.sp - 32#64 - 64#64 = s0.sp - 96#64 := by bv_arith
  wp_call harch (s0.readReg64 (.gpr 0#5))
  have hvm2 : VmPreserved s0 sf := hvm1.trans ‹_›
  clear hvm1
  apply sepWP_seg_ls_vm (Q := (blkPC_47).rebase (blkPl_47).base (hooksException ext))
    blkLib_eq_47 (mid := lsρ lsMemcpySym)
  intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm3 : VmPreserved s0 _ :=
    hvm2.trans (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
  clear hvm2
  apply ProofLib.SepWP.replace_pre (by sep_focus)
    (pointsTo64_memRegion_336_entails_344
      (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
  apply ProofLib.SepWP.replace_pre (by sep_focus)
    (p2_cells_sub32_4_merge_placed s0.sp _ _ _ _)
  rw [← h_1]
  wp_call hmc (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
  simp only [h_1, State.setMem_setMem] at *
  have hvm_f : VmPreserved s0 sf_1 := hvm3.trans ‹_›
  wp_done

/-- `SessionRecord::promote_state` (`lsmpl.base 47`, 0-stack `framelessMemcpyBudgetSpec`) on
`stageP1ProgPlaced ext`. -/
theorem promote_state_empty_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmptySpec) :=
  ls_subroutine_ok_of_block (i := 518) (j := 47)
    (promote_state_empty_placed_ok ext hMemcpy) (by decide)

/-- 4 KiB-stacked `SessionRecord::promote_state` (`lsmpl.base 47`, `p2Memcpy4KSpec`) on
`stageP1ProgPlaced ext`. -/
theorem promote_state_empty_4k_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec) := by
  have h47 : subroutine_ok ((blkPC_47).rebase (blkPl_47).base ext) (blkPl_47).base
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec) := by
    dsimp only [promoteStateEmpty4KSpec, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.promoteStateEmpty4KSpec]
    wp_init x s0
    obtain ⟨recPtr, srcPtr, bs⟩ := x
    dsimp only [withLsCodeLoaded] at *
    subst h_2 h_3
    have harch := ls_subroutine_ok_cl_of_plain
      (callerProg := (blkPC_47).rebase (blkPl_47).base ext) (entry := lsmpl.base 51)
      (archive_current_state_inner_empty_vm_placed_ok ext)
    simp only [withLsCl, withVmPreserved, archiveCurrentStateInnerEmptySpec] at harch
    have hmc : subroutine_ok ((blkPC_47).rebase (blkPl_47).base ext) (lsρ lsMemcpySym) _ :=
      ls_hook_ok_of_mem hMemcpy
    rw (occs := .pos [1]) [p2_stackAt_promote_state_split_placed s0.sp]
    have hc4 : cells (s0.sp - 32#64) 4 =
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
          ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
          ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
      cells_unfold
    rw [hc4]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    wp_pull_exists
    apply SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk) h (mid := lsmpl.base 51)
    apply sepWP_seg_ls_vm (Q := (blkPC_47).rebase (blkPl_47).base (hooksException ext))
      blkLib_eq_47 (mid := lsmpl.base 51)
    intro _m_strip
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
    have hsp_sub : s0.sp - 32#64 - 64#64 = s0.sp - 96#64 := by bv_arith
    wp_call harch (s0.readReg64 (.gpr 0#5))
    have hvm2 : VmPreserved s0 sf := hvm1.trans ‹_›
    clear hvm1
    apply sepWP_seg_ls_vm (Q := (blkPC_47).rebase (blkPl_47).base (hooksException ext))
      blkLib_eq_47 (mid := lsρ lsMemcpySym)
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm3 : VmPreserved s0 _ :=
      hvm2.trans (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    clear hvm2
    apply ProofLib.SepWP.replace_pre (by sep_focus)
      (pointsTo64_memRegion_336_entails_344
        (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
    apply ProofLib.SepWP.replace_pre (by sep_focus)
      (p2_cells_sub32_4_merge_placed s0.sp _ _ _ _)
    refine SepWP.fold (Entails.of_eq (p2_stackAt_promote_state_split_placed s0.sp).symm)
      (by sep_focus) ?_
    rw [← h_1]
    wp_call hmc (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
    simp only [h_1, State.setMem_setMem] at *
    have hvm_f : VmPreserved s0 sf_1 := hvm3.trans ‹_›
    wp_done
  exact ls_subroutine_ok_of_block (i := 518) (j := 47) h47 (by decide)

theorem promote_state_empty_4k_of_frameless_placed_ok_at [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 47)
      (withLsCodeLoaded lsmpl promoteStateEmpty4KSpec) :=
  promoteStateEmptySpec_lscl_to_4K (promote_state_empty_placed_ok_at hMemcpy)

set_option maxHeartbeats 1200000 in
/-- 4 KiB-stacked `<kem::KeyPair>::from_public_and_private` (`Block 70`) under
`noAllocShimBudgetSpec`, `rustCliAllocBudgetSpec M A lim false`, and `p2Memcpy4KSpec`. -/
theorem kemKeyPairFromPubPriv_4k_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec) :
    subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext) (blkPl_70).base
      (kemKeyPairFromPubPrivOkSpec M A lim) := by
  simp only [kemKeyPairFromPubPrivOkSpec,
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpec,
    CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
    p2_stackAt_kemKeyPairFromPubPriv_placed,
    RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  cells_unfold
  wp_init xst s0
  obtain ⟨⟨pubPtr, pk, privPtr, sk, outPtr⟩, st⟩ := xst
  dsimp only at *
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left,
    bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  wp_pull_exists
  have hx0_eq : s0.readReg64 .x0 = pubPtr := by assumption
  have hx2_eq : s0.readReg64 .x2 = privPtr := by assumption
  have hx8_eq : s0.readReg64 .x8 = outPtr := by assumption
  subst hx0_eq hx2_eq hx8_eq
  have hshim_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext)
      (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
    ls_hook_ok_of_mem (hookSat_sessionShimBudget_of_noAllocShimBudget hShim)
  have halloc_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem hAlloc)
  have hmemcpy_ok : subroutine_ok ((blkPC_70).rebase (blkPl_70).base ext)
      (lsρ lsMemcpySym) _ :=
    ls_hook_ok_of_mem hMemcpy
  dsimp only [sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim_ok
  dsimp only [rustCliAllocNoOomSpec, AllocCallPreserved, PoolPreserved,
    Bool.false_eq_true, ↓reduceIte] at halloc_ok
  have hfit_all : FitsEvents M lim st kemKeyPairFromPubPrivEvents :=
    ‹FitsEnv M lim st KemKeyPairFromPubPrivEnv› _ rfl
  rw [kemKeyPairFromPubPrivEvents,
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivEvents,
    fitsEvents_append] at hfit_all
  rcases hfit_all with ⟨hfit1, hfit2⟩
  have hfe1 : FitsEvents M lim st [.alloc 1568] := by simpa [rustAllocEvents] using hfit1
  rcases hfe1 with ⟨⟨hwma1, henf1, hram1, hva1⟩, -⟩
  have hfe2 : FitsEvents M lim (M.stepEvents (rustAllocEvents 1568 1) st) [.alloc 3168] := by
    simpa [rustAllocEvents] using hfit2
  rcases hfe2 with ⟨⟨hwma2, henf2, hram2, hva2⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay1 : RustLayoutOk 1568 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hlay2 : RustLayoutOk 3168 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hpk_len : pk.length = 1568 := by assumption
  have hsk_len : sk.length = 3168 := by assumption
  rw [pointsToBytes_cons (s0.readReg64 (.gpr 0#5)),
    pointsToBytes_cons (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_apply
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (1568, 1, st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hpk_len]
  wp_call hmemcpy_ok (sf_1.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 0#5) + 1#64, pk)
  simp only [hpk_len] at *
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  wp_simp_pre [wp_norm]
  wp_call hshim_ok ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  wp_simp_pre [wp_norm]
  wp_apply with (3168, 1, M.stepEvents (rustAllocEvents 1568 1) st)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  wp_simp_pre [wp_norm]
  rw [← hsk_len]
  wp_call hmemcpy_ok (sf_4.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 2#5) + 1#64, sk)
  simp only [hsk_len] at *
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  wp_steps_sync_pool (s0.readReg64 (.gpr 30#5))
  simp only [kemKeyPairFromPubPrivEvents,
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivEvents,
    AllocCostModel.stepEvents_append]
  wp_done

/-- 4 KiB-stacked `<kem::KeyPair as KeyPairSerde>::from_public_and_private` (`lsmpl.base 113`) on
`stageP1ProgPlaced ext`. -/
theorem kemKeyPairSerde_4k_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext lsMemcpySym p2Memcpy4KSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim)) := by
  have h113 : subroutine_ok ((blkPC_113).rebase (blkPl_113).base ext) (blkPl_113).base
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim)) := by
    have hinner := ls_subroutine_ok_of_block
      (callerProg := (blkPC_113).rebase (blkPl_113).base ext)
      (entry := lsmpl.base 70)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (kemKeyPairFromPubPriv_4k_placed_ok hShim hAlloc hMemcpy))
    exact subroutine_ok_of_b (by simp only [arm64_norm]; rfl)
      (by simp only [arm64_norm])
      rfl (by
        intro x s pc
        dsimp only [withLsCodeLoaded, kemKeyPairFromPubPrivOkSpec,
          LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.kemKeyPairFromPubPrivOkSpec,
          CryptoVerification.E2E.Pqxdh.ResponderStore.kemKeyPairFromPubPrivOkSpec,
          RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
        rw [A.pool_setPC lim x.2 s pc]
        cases s; rfl)
      hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)
  exact ls_subroutine_ok_of_block (i := 518) (j := 113) h113 (by decide)

/-- 0-stack `<kem::KeyPair as KeyPairSerde>::from_public_and_private` (`lsmpl.base 113`,
`sessionShimBudgetSpec` + `sessionMemcpyRegionBudgetSpec`) on `stageP1ProgPlaced ext`. -/
theorem kemKeyPairSerde_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 113)
      (withLsCodeLoaded lsmpl (kemKeyPairFromPubPrivOkSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := 518) (j := 113)
    (kemKeyPairSerde_placed_ok hShim hAlloc hMemcpy) (by decide)

end PlacedPureAnd4KCallees

/-! ## 3. Drop Glue & `is_same_account` Bridges on `stageP1ProgPlaced ext` -/

/-- `drop_glue::<SignalProtocolError> [local#2]` (`lsmpl.base 511`) on `stageP1ProgPlaced ext`. -/
theorem drop_spe2_placed_ok_on_stageP1 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :=
  drop_spe2_placed_ok_at (callerProg := stageP1ProgPlaced ext) (i := 518) hDealloc (by decide)

/-- `drop_glue::<SessionStructure> [local#4]` (`lsmpl.base 512`) on `stageP1ProgPlaced ext`. -/
theorem drop_session_structure3_placed_ok_on_stageP1 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at hDealloc (by decide)

/-- `<IdentityKey>::is_same_account` (`lsmpl.base 17`, `withVmPreserved`) on
`stageP1ProgPlaced ext`. -/
theorem isSameAccount_placed_ok_on_stageP1 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBb : ext lsBlackBoxU8Sym = some blackBoxHook)
    (hUuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base ext) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse)))) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)) :=
  isSameAccountEqDistinct_placed_ok_at A hBb hUuid (by decide)

/-- 4K/`Ext` `<IdentityKey>::is_same_account` (`lsmpl.base 17`, `withVmPreserved`) on
`stageP1ProgPlaced ext`. -/
theorem isSameAccount_4k_placed_ok_on_stageP1 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBb : ext lsBlackBoxU8Sym = some blackBoxHook)
    (hUuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base ext) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse)))) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A uuidTryParse)) :=
  isSameAccountDistinctSpec_lscl_to_ext (isSameAccount_placed_ok_on_stageP1 hBb hUuid)

/-! ## 4. Cross-Block `initialize_bob_session` (`Block 75`) Bridges on `stageP1ProgPlaced ext` -/

/-- Cross-block `SepWPp` transfer from a non-mutated callee block `j` (`calleeProg`) to any
`callerProg` sharing `H` when `LibsignalCodeLoaded lsmpl s.mem` holds. -/
theorem ls_sepWPp_of_block [LibsignalPlacement]
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee : IsLsBlockProg calleeProg j H]
    {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp calleeProg ret s P Q Qp oom)
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWPp callerProg ret s P Q Qp oom := by
  intro R hm _hcallerL
  have hQL : calleeProg.CodeLoaded s.mem :=
    hcallee.eq_blockProgram ▸ hcl j (by omega) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout⟩ := h R hm hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact ⟨sf, Steps.of_sameHooks hext hsvc hstepsQ, hout⟩

/-- Rejecting run of `initialize_bob_session` (`lsmpl.base 75`,
`initializeBobSessionErrPlacedSpec P A lim AcceptErrEnv`) on `stageP1ProgPlaced ext` from
`h_accept` on `lsProg_75 ext`. -/
theorem initializeBobSession_err_placed_ok_on_stageP1 [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErrPlacedSpec P A lim AcceptErrEnv) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_placed_ok_of_accept h_accept)
      (by decide) (by decide) (by decide))

/-- 4K/`Ext` rejecting run of `initialize_bob_session` (`lsmpl.base 75`,
`initializeBobSessionErr4KPlacedSpec P A lim AcceptErrEnv`) on `stageP1ProgPlaced ext` from
`h_accept`. -/
theorem initializeBobSession_err_4k_placed_ok_on_stageP1 [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErr4KPlacedSpec P A lim AcceptErrEnv) :=
  initializeBobSessionErrPlacedSpec_to_4K (initializeBobSession_err_placed_ok_on_stageP1 h_accept)

/-- Owned-error rejecting run of `initialize_bob_session` (`lsmpl.base 75`,
`initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv`) on `stageP1ProgPlaced ext` from
`h_accept`. -/
theorem initializeBobSession_err_owned_placed_ok_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv) :=
  subroutine_ok_withLsCodeRoLoaded_of_rocl
    (ls_subroutine_ok_rocl_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_owned_placed_ok_of_accept h_accept)
      (by decide) (by decide) (by decide))

/-- 4K/`Ext` owned-error rejecting run of `initialize_bob_session` (`lsmpl.base 75`,
`initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv`) on `stageP1ProgPlaced ext`. -/
theorem initializeBobSession_err_owned_4k_placed_ok_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv) :=
  initializeBobSessionErrOwnedPlacedSpec_to_4K
    (initializeBobSession_err_owned_placed_ok_on_stageP1 h_accept)

private theorem p2_initBobErrOwnedAt_to_initBobErrAt_placed (A : RustAlloc) (outPtr : BitVec 64) :
    initBobErrOwnedAt A outPtr ∗ anyHeap ⊢ initBobErrAt outPtr ∗ anyHeap := by
  unfold initBobErrOwnedAt
  conv =>
    lhs
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.sepExists_elim fun errTag => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  rw [sepConj_left_comm]
  refine Entails.pure_left fun herr => ?_
  have h1 :
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        (((outPtr + 8#64) ↦₆₄ errTag) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗
          (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
            (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
              (pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
                (memRegion (outPtr + 56#64) 288 ∗ anyHeap)))))))) =
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        ((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 288) ∗
      (anyHeap ∗ pqxdhAcceptErrPayloadAt A errTag w2 w3 w4) := by sep_ac_rfl
  rw [h1]
  exact sepConj_mono (initBobErrAt_merge outPtr errTag w2 w3 w4 w5 w6 herr) (entails_anyHeap _)

/-- Weaken `initializeBobSessionErrOwnedPlacedSpec` to unowned `initializeBobSessionErrPlacedSpec`. -/
theorem initializeBobSession_err_of_err_owned_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok prog entry (initializeBobSessionErrPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  dsimp only [initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
    withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hnone : acceptKeys P g.inp = none := hpre.1.2.2.2.2.2.2.2.2.2.1
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact hpre
  · dsimp only [initializeBobSessionErrOwnedPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      initializeBobSessionErrPlacedSpec, initializeBobSessionErrInnerPlacedSpec,
      initializeBobSessionInnerPlacedSpec, withLsCodeRoLoaded] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    rw [satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hpost⟩ := hpost
    refine ⟨evs, ?_⟩
    rw [hnone]
    dsimp only
    refine Satisfies.mono ?_ hpost
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ?_))
    exact sepConj_mono_left (p2_initBobErrOwnedAt_to_initBobErrAt_placed A.repAlloc g.outPtr)

/-- 4K/`Ext` weakening from `initializeBobSessionErrOwnedPlacedSpec` to
`initializeBobSessionErr4KPlacedSpec`. -/
theorem initializeBobSession_err_4k_of_err_owned_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    subroutine_ok prog entry (initializeBobSessionErr4KPlacedSpec P A lim AcceptErrEnv) :=
  initializeBobSessionErrPlacedSpec_to_4K (initializeBobSession_err_of_err_owned_placed h)

/-- Envelope-parametric SPQR V1 `initialize_bob_session` success
(`InitializeBobV1OkPlacedOfEnv`) on `stageP1ProgPlaced ext` from `h_accept` and `hinit` on
`lsProg_75 ext`, for any `BobInitEnv : Bytes → List AllocEvent → Prop` independent of entry `sp0`. -/
theorem initializeBobSession_ok_v1_of_env_placed_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1OkPlacedOfEnv P A lim F
      (fun inp drKey => SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hCode hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hinit_fun : InitEnv (bobSpqrGhost s0.sp drKey.pqrKey) = BobInitEnv drKey.pqrKey :=
    funext fun evs => propext (hinit_eq s0.sp drKey.pqrKey evs)
  have henv_eq :
      InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey =
        SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) := by
    unfold InitBobV1EnvOfEnv; rw [hinit_fun]
  have hfits' : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey) :=
    henv_eq ▸ hfits
  have h75 := ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) hCode.1
    (initializeBobSession_ok_v1_placed_of_accept_of_session (Qp := Qp)
      hWF (hookSat_sessionShimBudget_of_noAllocShimBudget hShim) hAlloc hDealloc hMemcpy
      h_accept hinit s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
      ratchetKeyPairPtr outPtr drKey Frame hCode hfits' hrun hpc hsp hpqr
      hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs,
    localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
    ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
    hevs, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := h75 R hm hL
  · have hevs' :
        SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) evs :=
      henv_eq ▸ hevs
    exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs',
      localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

/-- 4K/`Ext` envelope-parametric SPQR V1 `initialize_bob_session` success on `stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_of_env_4k_placed_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1OkPlaced4KOfEnv P A lim F
      (fun inp drKey => SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  InitializeBobV1OkPlacedOfEnv.to_4K
    (initializeBobSession_ok_v1_of_env_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpy h_accept hinit hinit_eq)

/-- Default SPQR V1 `initialize_bob_session` success (`AcceptSuccessEnv`) on `stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_placed_on_stageP1 [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptSuccessEnv))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1OkPlaced P A lim F ext :=
  initializeBobSession_ok_v1_of_env_placed_on_stageP1
    hWF hShim hAlloc hDealloc hMemcpy h_accept hinit (fun _ _ _ => Iff.rfl)

/-- 4K/`Ext` SPQR V1 `initialize_bob_session` success (`AcceptSuccessEnv`) on `stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_4k_placed_on_stageP1 [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptSuccessEnv))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1OkPlaced4K P A lim F ext :=
  InitializeBobV1OkPlaced.to_4K
    (initializeBobSession_ok_v1_placed_on_stageP1 hWF hShim hAlloc hDealloc hMemcpy h_accept hinit)

/-- SPQR V1 `initialize_bob_session` success (`AcceptOptFieldsEnv P`) on `stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_optFields_placed_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim (AcceptOptFieldsEnv P)))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1OkPlacedOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  initializeBobSession_ok_v1_of_env_placed_on_stageP1
    hWF hShim hAlloc hDealloc hMemcpy h_accept hinit (fun _ _ _ => Iff.rfl)

/-- 4K/`Ext` SPQR V1 `initialize_bob_session` success (`AcceptOptFieldsEnv P`) on
`stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_optFields_4k_placed_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim (AcceptOptFieldsEnv P)))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1OkPlaced4KOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  InitializeBobV1OkPlacedOfEnv.to_4K
    (initializeBobSession_ok_v1_optFields_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpy h_accept hinit)

/-! ## 5. `StageP2PureCalleesPlaced*` Bundle Constructors -/

/-- Envelope-parametric constructor for `StageP2PureCalleesPlacedOfEnv` on `stageP1ProgPlaced ext`. -/
theorem stageP2PureCalleesPlacedOfEnv_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptOkEnv AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse)))
    (h_accept_ok : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptOkEnv))
    (h_accept_err : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptErrEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    StageP2PureCalleesPlacedOfEnv P A lim F
      (fun inp drKey => SeqEnv (AcceptOkEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      AcceptErrEnv ext where
  publicKeySerialize := p2_publicKeySerialize_of_hooks_placed hShim hAlloc
  promoteMatchingSessionEmpty := promote_matching_session_empty_placed_ok_at
  curveKeyPairSerde := curveKeyPairSerde_placed_ok_at
  kemKeyPairSerde := kemKeyPairSerde_4k_placed_ok_at hShim hAlloc hMemcpy4K
  preKeyRecordKeyPair := preKeyRecordKeyPair_placed_ok_at
  dropSpe2 := drop_spe2_placed_ok_on_stageP1 hDealloc
  isSameAccount := hSame
  initializeBobV1 :=
    initializeBobSession_ok_v1_of_env_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpySess h_accept_ok hinit hinit_eq
  initializeBobErr := initializeBobSession_err_placed_ok_on_stageP1 h_accept_err
  promoteStateEmpty := promote_state_empty_placed_ok_at hMemcpy
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_placed_ok
  dropSessionStructure3 := drop_session_structure3_placed_ok_on_stageP1 hDealloc

/-- Envelope-parametric constructor for `StageP2PureCalleesPlaced4KOfEnv` on `stageP1ProgPlaced ext`. -/
theorem stageP2PureCalleesPlaced4KOfEnv_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptOkEnv AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse)))
    (h_accept_ok : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptOkEnv))
    (h_accept_err : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptErrEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    StageP2PureCalleesPlaced4KOfEnv P A lim F
      (fun inp drKey => SeqEnv (AcceptOkEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      AcceptErrEnv ext where
  publicKeySerialize := p2_publicKeySerialize_of_hooks_placed hShim hAlloc
  promoteMatchingSessionEmpty := promote_matching_session_empty_placed_ok_at
  curveKeyPairSerde := curveKeyPairSerde_placed_ok_at
  kemKeyPairSerde := kemKeyPairSerde_4k_placed_ok_at hShim hAlloc hMemcpy4K
  preKeyRecordKeyPair := preKeyRecordKeyPair_placed_ok_at
  dropSpe2 := drop_spe2_placed_ok_on_stageP1 hDealloc
  isSameAccount := hSame
  initializeBobV1 :=
    initializeBobSession_ok_v1_of_env_4k_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpySess h_accept_ok hinit hinit_eq
  initializeBobErr := initializeBobSession_err_4k_placed_ok_on_stageP1 h_accept_err
  promoteStateEmpty := promote_state_empty_4k_placed_ok_at hMemcpy4K
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_placed_ok
  dropSessionStructure3 := drop_session_structure3_placed_ok_on_stageP1 hDealloc

/-- Construct `StageP2PureCalleesPlaced` (`InitializeBobV1Env F`) on `stageP1ProgPlaced ext`. -/
theorem stageP2PureCalleesPlaced_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse)))
    (h_accept_ok : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptSuccessEnv))
    (h_accept_err : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptErrEnv))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    StageP2PureCalleesPlaced P A lim F AcceptErrEnv ext :=
  stageP2PureCalleesPlacedOfEnv_of_hooks
    hWF hShim hAlloc hDealloc hMemcpy hMemcpySess hMemcpy4K hSame
    h_accept_ok h_accept_err hinit (fun _ _ _ => Iff.rfl)

/-- Construct `StageP2PureCalleesPlaced4K` (`InitializeBobV1Env F`) on `stageP1ProgPlaced ext`. -/
theorem stageP2PureCalleesPlaced4K_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse)))
    (h_accept_ok : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptSuccessEnv))
    (h_accept_err : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim AcceptErrEnv))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext :=
  stageP2PureCalleesPlaced4KOfEnv_of_hooks
    hWF hShim hAlloc hDealloc hMemcpySess hMemcpy4K hSame
    h_accept_ok h_accept_err hinit (fun _ _ _ => Iff.rfl)

/-- Single-`h_accept` constructor for `StageP2PureCalleesPlacedOfEnv` at `AcceptOptFieldsEnv P`. -/
theorem stageP2PureCalleesPlacedOfEnv_of_optFields_hooks [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse)))
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim (AcceptOptFieldsEnv P)))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    StageP2PureCalleesPlacedOfEnv P A lim F
      (InitializeBobV1OptFieldsEnv P F) (AcceptOptFieldsEnv P) ext :=
  stageP2PureCalleesPlacedOfEnv_of_hooks
    hWF hShim hAlloc hDealloc hMemcpy hMemcpySess hMemcpy4K hSame
    h_accept h_accept hinit (fun _ _ _ => Iff.rfl)

/-- Single-`h_accept` 4K/`Ext` constructor for `StageP2PureCalleesPlaced4KOfEnv` at
`AcceptOptFieldsEnv P`. -/
theorem stageP2PureCalleesPlaced4KOfEnv_of_optFields_hooks [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse)))
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec P A lim (AcceptOptFieldsEnv P)))
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    StageP2PureCalleesPlaced4KOfEnv P A lim F
      (InitializeBobV1OptFieldsEnv P F) (AcceptOptFieldsEnv P) ext :=
  stageP2PureCalleesPlaced4KOfEnv_of_hooks
    hWF hShim hAlloc hDealloc hMemcpySess hMemcpy4K hSame
    h_accept h_accept hinit (fun _ _ _ => Iff.rfl)

/-! ## 6. `StageP2MemInv` / `LibsignalFrozen` / `[LibsignalFullPlacement]` Bridges & `StageP2BaseCalleesPlaced4K.of_hooks` -/

theorem initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F BobV1Env ext1 bobV1Stk) :
    InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F BobV1Env ext2 bobV1Stk := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  exact SepWPp.of_trapsOnly hT
    (h s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits)

theorem initializeBobV1MemInvOkAtPlaced_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1MemInvOkAtPlaced Φ P A lim F ext1 bobV1Stk) :
    InitializeBobV1MemInvOkAtPlaced Φ P A lim F ext2 bobV1Stk :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1MemInvOkPlacedOfEnv_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1MemInvOkPlacedOfEnv Φ P A lim F BobV1Env ext1) :
    InitializeBobV1MemInvOkPlacedOfEnv Φ P A lim F BobV1Env ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1MemInvOkPlaced_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1MemInvOkPlaced Φ P A lim F ext1) :
    InitializeBobV1MemInvOkPlaced Φ P A lim F ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1MemInvOkPlaced4KOfEnv_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1MemInvOkPlaced4KOfEnv Φ P A lim F BobV1Env ext1) :
    InitializeBobV1MemInvOkPlaced4KOfEnv Φ P A lim F BobV1Env ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1MemInvOkPlaced4K_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1MemInvOkPlaced4K Φ P A lim F ext1) :
    InitializeBobV1MemInvOkPlaced4K Φ P A lim F ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1FrozenOkAtPlacedOfEnv_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkAtPlacedOfEnv P A lim F BobV1Env ext1 bobV1Stk) :
    InitializeBobV1FrozenOkAtPlacedOfEnv P A lim F BobV1Env ext2 bobV1Stk :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1FrozenOkAtPlaced_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)} {bobV1Stk : Nat}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkAtPlaced P A lim F ext1 bobV1Stk) :
    InitializeBobV1FrozenOkAtPlaced P A lim F ext2 bobV1Stk :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1FrozenOkPlacedOfEnv_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkPlacedOfEnv P A lim F BobV1Env ext1) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F BobV1Env ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1FrozenOkPlaced_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkPlaced P A lim F ext1) :
    InitializeBobV1FrozenOkPlaced P A lim F ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1FrozenOkPlaced4KOfEnv_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext1) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem initializeBobV1FrozenOkPlaced4K_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : InitializeBobV1FrozenOkPlaced4K P A lim F ext1) :
    InitializeBobV1FrozenOkPlaced4K P A lim F ext2 :=
  initializeBobV1MemInvOkAtPlacedOfEnv_of_trapsOnly hT h

theorem stageP2BaseCalleesPlaced4K_of_trapsOnly [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (stageP1ProgPlaced ext1) (stageP1ProgPlaced ext2))
    (h : StageP2BaseCalleesPlaced4K A lim ext1) :
    StageP2BaseCalleesPlaced4K A lim ext2 where
  publicKeySerialize := subroutine_ok.of_trapsOnly hT h.publicKeySerialize
  promoteMatchingSessionEmpty := subroutine_ok.of_trapsOnly hT h.promoteMatchingSessionEmpty
  curveKeyPairSerde := subroutine_ok.of_trapsOnly hT h.curveKeyPairSerde
  kemKeyPairSerde := subroutine_ok.of_trapsOnly hT h.kemKeyPairSerde
  preKeyRecordKeyPair := subroutine_ok.of_trapsOnly hT h.preKeyRecordKeyPair
  dropSpe2 := subroutine_ok.of_trapsOnly hT h.dropSpe2
  isSameAccount := subroutine_ok.of_trapsOnly hT h.isSameAccount
  promoteStateEmpty := subroutine_ok.of_trapsOnly hT h.promoteStateEmpty
  dropProcessPrekeyImplState1 := subroutine_ok.of_trapsOnly hT h.dropProcessPrekeyImplState1
  dropSessionStructure3 := subroutine_ok.of_trapsOnly hT h.dropSessionStructure3

/-- Stack-frame widening from `InitializeBobV1MemInvOkPlacedOfEnv`
(`stageP2bStack + 0x700`) to `InitializeBobV1MemInvOkPlaced4KOfEnv` (`768 + pqxdhEntryStackExt`). -/
theorem p2_initBobV1MemInvPlacedOfEnv_to_4K [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : InitializeBobV1MemInvOkPlacedOfEnv Φ P A lim F BobV1Env ext) :
    InitializeBobV1MemInvOkPlaced4KOfEnv Φ P A lim F BobV1Env ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (stageP2bStack + 0x700))
  have hsplit := p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (stageP2bStack + 0x700) (by decide) (by decide)
  have hcall := h (st := st) (Qp := Qp) s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
    ratchetKeyPairPtr outPtr drKey (F_stk ∗ Frame)
    hΦ hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  intro R hm hL
  have hm' : s0.mem ⊨
      (bobParamsFieldsAt argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr inp ikBPk spkBPk 0#8 ∗
        memRegion outPtr 344 ∗ lsLogFilterAddr ↦₆₄ 0#64 ∗
        stackAt s0.sp (stageP2bStack + 0x700) ∗ A.pool lim st s0 ∗ (F_stk ∗ Frame)) ∗ R := by
    refine Satisfies.of_eq hm ?_; dsimp only [F_stk]; rw [hsplit]; ac_rfl
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr,
    baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7,
    hPf, hst'⟩ | hpan⟩ := hcall R hm' hL
  · refine ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs, localIkBoxPtr,
      remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr, ratchetPubBoxPtr, ratchetPrivBoxPtr,
      chainKeyBoxPtr, spqrCap, spqrBufPtr, pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7,
      Entails.trans hPf (Entails.of_eq ?_), hst'⟩⟩
    dsimp only [F_stk]; rw [hsplit]; ac_rfl
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem p2_initBobV1MemInvPlaced_to_4K [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1MemInvOkPlaced Φ P A lim F ext) :
    InitializeBobV1MemInvOkPlaced4K Φ P A lim F ext :=
  p2_initBobV1MemInvPlacedOfEnv_to_4K h

theorem p2_initBobV1FrozenPlacedOfEnv_to_4K [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : InitializeBobV1FrozenOkPlacedOfEnv P A lim F BobV1Env ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext :=
  p2_initBobV1MemInvPlacedOfEnv_to_4K h

theorem p2_initBobV1FrozenPlaced_to_4K [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (h : InitializeBobV1FrozenOkPlaced P A lim F ext) :
    InitializeBobV1FrozenOkPlaced4K P A lim F ext :=
  p2_initBobV1MemInvPlacedOfEnv_to_4K h

/-- Closed `[LibsignalFullPlacement]` rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `withLsCodeRoLoaded lsmpl (initializeBobSessionErrFrozenPlacedSpec ...)`)
on `stageP1ProgPlaced ext`, discharging Block `79` (`Pqxdh::accept`) via `withLsFrozen`. -/
theorem initializeBobSession_err_full_placed_ok_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_full_placed_ok hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem initializeBobSession_err_full_placed_ok_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_full_placed_ok_std hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Closed `[LibsignalFullPlacement]` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `withLsCodeRoLoaded lsmpl (initializeBobSessionErrOwnedFrozenPlacedSpec ...)`)
on `stageP1ProgPlaced ext`, discharging Block `79` (`Pqxdh::accept`) via `withLsFrozen`. -/
theorem initializeBobSession_err_owned_full_placed_ok_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_owned_full_placed_ok hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

theorem initializeBobSession_err_owned_full_placed_ok_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim (AcceptOptFieldsEnv P))) := by
  have hbase :=
    ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (initializeBobSession_err_owned_full_placed_ok_std hWF hP hH h_memcpy)
  refine subroutine_ok_map hbase ?_
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost⟩
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

/-- Stack-frame widening from `withLsCodeRoLoaded lsmpl (initializeBobSessionErrOwnedFrozenPlacedSpec ...)`
to `StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec`. -/
theorem p2_errOwned_frozen_to_defs4K_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim AcceptErrEnv))) :
    subroutine_ok prog entry
      (StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec P A lim AcceptErrEnv) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  let F_stk : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 (768 + pqxdhEntryStackExt))
      ((768 + pqxdhEntryStackExt) - (768 + pqxdhEntryStack))
  dsimp only [StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec,
    StageP2DefsPlacedBudget.initializeBobSessionErrOwnedMemInv4KPlacedSpec,
    withLsCodeRoLoaded, withBobMemInv] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfr, hpre⟩
  dsimp only [initializeBobSessionErrOwned4KInnerPlacedSpec] at hpre
  rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
    (768 + pqxdhEntryStack) (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(g, st), F_stk ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedFrozenPlacedSpec, withLsCodeRoLoaded, withLsFrozen]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hfr, ?_⟩
    dsimp only [initializeBobSessionErrOwnedInnerPlacedSpec, F_stk]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpure, ?_⟩
    refine Satisfies.of_eq hmem ?_
    ac_rfl
  · dsimp only [StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec,
      StageP2DefsPlacedBudget.initializeBobSessionErrOwnedMemInv4KPlacedSpec,
      initializeBobSessionErrOwned4KInnerPlacedSpec,
      initializeBobSessionErrOwnedFrozenPlacedSpec,
      initializeBobSessionErrOwnedInnerPlacedSpec,
      withLsCodeRoLoaded, withBobMemInv, withLsFrozen, F_stk] at hpost ⊢
    rw [sepExists_sepConj_left] at hpost ⊢
    rw [satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hpost⟩ := hpost
    refine ⟨evs, ?_⟩
    rw [p2_stackAt_split_of_le s0.sp (768 + pqxdhEntryStackExt)
      (768 + pqxdhEntryStack) (by decide) (by decide)]
    refine Satisfies.of_eq hpost ?_
    ac_rfl

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec`) on
`stageP1ProgPlaced ext`. -/
theorem initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  p2_errOwned_frozen_to_defs4K_placed
    (initializeBobSession_err_owned_full_placed_ok_on_stageP1 hWF hP hH h_memcpy)

theorem initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  p2_errOwned_frozen_to_defs4K_placed
    (initializeBobSession_err_owned_full_placed_ok_on_stageP1_std hWF hP hH h_memcpy)

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` owned-error rejecting run of `initialize_bob_session`
(`lsmpl.base 75`, `Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec`) on
`stageP1ProgPlaced ext`. -/
theorem initializeBobSession_err_owned_4k_full_placed_ok_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  of_stageP2Defs_errOwned4K_frozen_placed
    (initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1 hWF hP hH h_memcpy)

theorem initializeBobSession_err_owned_4k_full_placed_ok_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (h_memcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec
        P A lim (AcceptOptFieldsEnv P)) :=
  of_stageP2Defs_errOwned4K_frozen_placed
    (initializeBobSession_err_owned_4k_defs_full_placed_ok_on_stageP1_std hWF hP hH h_memcpy)

/-- `LibsignalFrozen`-guarded envelope-parametric SPQR V1 `initialize_bob_session` success
(`InitializeBobV1FrozenOkPlacedOfEnv`) on `stageP1ProgPlaced ext` from `h_accept` and `hinit` on
`lsProg_75 ext`. -/
theorem initializeBobSession_ok_v1_of_env_frozen_placed_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F
      (fun inp drKey => SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hinit_fun : InitEnv (bobSpqrGhost s0.sp drKey.pqrKey) = BobInitEnv drKey.pqrKey :=
    funext fun evs => propext (hinit_eq s0.sp drKey.pqrKey evs)
  have henv_eq :
      InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey =
        SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) := by
    unfold InitBobV1EnvOfEnv; rw [hinit_fun]
  have hfits' : FitsEnv M lim st (InitBobV1EnvOfEnv AcceptEnv InitEnv s0.sp inp drKey.pqrKey) :=
    henv_eq ▸ hfits
  have h75 := ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
    (initializeBobSession_ok_v1_frozen_placed_of_accept_of_session (Qp := Qp)
      hWF (hookSat_sessionShimBudget_of_noAllocShimBudget hShim) hAlloc hDealloc hMemcpy
      h_accept (initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded hinit)
      s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
      ratchetKeyPairPtr outPtr drKey Frame hfr hfits' hrun hpc hsp hpqr
      hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs,
    localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
    ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
    hevs, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := h75 R hm hL
  · have hevs' :
        SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) evs :=
      henv_eq ▸ hevs
    exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs',
      localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem initializeBobSession_ok_v1_of_env_4k_frozen_placed_on_stageP1 [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptEnv : AcceptKeysInput → List AllocEvent → Prop}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} (hWF : StructuralPrims P)
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (h_accept : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (pqxdhAcceptOptFieldsFrozenPlacedSpec P A lim AcceptEnv))
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F
      (fun inp drKey => SeqEnv (AcceptEnv inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_of_env_frozen_placed_on_stageP1
      hWF hShim hAlloc hDealloc hMemcpy h_accept hinit hinit_eq)

/-- Closed `[LibsignalFullPlacement]` envelope-parametric SPQR V1 `initialize_bob_session` success
(`InitializeBobV1FrozenOkPlacedOfEnv`) on `stageP1ProgPlaced ext`, discharging Block `79`
(`Pqxdh::accept`) via `withLsFrozen` and taking only the `spqr::initial_state` seam (`LibsignalFrozen`). -/
theorem initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hinit_fun : InitEnv (bobSpqrGhost s0.sp drKey.pqrKey) = BobInitEnv drKey.pqrKey :=
    funext fun evs => propext (hinit_eq s0.sp drKey.pqrKey evs)
  have henv_eq :
      InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey =
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) := by
    unfold InitBobV1EnvOfEnv; rw [hinit_fun]
  have hfits' :
      FitsEnv M lim st (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey) :=
    henv_eq ▸ hfits
  have h75 := ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
    (initializeBobSession_ok_v1_full_placed_of_env_of_session (Qp := Qp)
      hWF hP hH hMemcpy hinit s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
      ratchetKeyPairPtr outPtr drKey Frame hfr hfits' hrun hpc hsp hpqr
      hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs,
    localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
    ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
    hevs, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := h75 R hm hL
  · have hevs' :
        SeqEnv (AcceptOptFieldsEnv P inp)
          (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) evs :=
      henv_eq ▸ hevs
    exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs',
      localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

/-- Closed `[LibsignalFullPlacement]` envelope-parametric SPQR V1 `initialize_bob_session` success
on `stageP1ProgPlaced ext` taking `InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl)`. -/
theorem initializeBobSession_ok_v1_full_placed_of_env_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit
    hWF hP hH hMemcpy (initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded hinit) hinit_eq

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` envelope-parametric SPQR V1 `initialize_bob_session`
success on `stageP1ProgPlaced ext`. -/
theorem initializeBobSession_ok_v1_4k_full_placed_of_env_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_of_env_on_stageP1
      hWF hP hH hMemcpy hinit hinit_eq)

theorem initializeBobSession_ok_v1_4k_full_placed_of_env_on_stageP1_of_frozenInit
    [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalFrozen lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit
      hWF hP hH hMemcpy hinit hinit_eq)

theorem initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext := by
  intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
    drKey Frame hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc hfits
  have hinit_fun : InitEnv (bobSpqrGhost s0.sp drKey.pqrKey) = BobInitEnv drKey.pqrKey :=
    funext fun evs => propext (hinit_eq s0.sp drKey.pqrKey evs)
  have henv_eq :
      InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey =
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) := by
    unfold InitBobV1EnvOfEnv; rw [hinit_fun]
  have hfits' :
      FitsEnv M lim st (InitBobV1EnvOfEnv (AcceptOptFieldsEnv P) InitEnv s0.sp inp drKey.pqrKey) :=
    henv_eq ▸ hfits
  have h75 := ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
    (initializeBobSession_ok_v1_full_placed_of_env_std (Qp := Qp)
      hWF hP hH hMemcpy (initialStateFrozenPlacedOkOfEnv_of_codeRoLoaded hinit)
      s0 st inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr
      ratchetKeyPairPtr outPtr drKey Frame hfr hfits' hrun hpc hsp hpqr
      hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc', hrun', Pf, hmf, evs,
    localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
    ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
    pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
    hevs, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩ | hpan⟩ := h75 R hm hL
  · have hevs' :
        SeqEnv (AcceptOptFieldsEnv P inp)
          (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv) evs :=
      henv_eq ▸ hevs
    exact ⟨sf, hst, Or.inl ⟨hpc', hrun', Pf, hmf, evs, hevs',
      localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr,
      ratchetPubBoxPtr, ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr,
      pad_f4, c0, c1, c2, c3, c4, d0, d1, d2,
      hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, hst'⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

theorem initializeBobSession_ok_v1_4k_full_placed_of_env_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobInitEnv : Bytes → List AllocEvent → Prop}
    {InitEnv : InitialStateGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOkOfEnv M (LibsignalCodeRoLoaded lsmpl) A lim F InitEnv ext)
    (hinit_eq : ∀ sp0 pqrKey evs, InitEnv (bobSpqrGhost sp0 pqrKey) evs ↔ BobInitEnv pqrKey evs) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F
      (fun inp drKey =>
        SeqEnv (AcceptOptFieldsEnv P inp) (SeqEnv (BobInitEnv drKey.pqrKey) InitBobSessionBuildEnv))
      ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_std
      hWF hP hH hMemcpy hinit hinit_eq)

/-- Closed `[LibsignalFullPlacement]` SPQR V1 `initialize_bob_session` success at
`InitializeBobV1OptFieldsEnv P F` on `stageP1ProgPlaced ext` (`sessionMemcpyRegionBudgetSpec`). -/
theorem initializeBobSession_ok_v1_full_placed_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1
    hWF hP hH hMemcpy hinit (fun _ _ _ => Iff.rfl)

theorem initializeBobSession_ok_v1_full_placed_on_stageP1_of_frozenInit [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_of_frozenInit
    hWF hP hH hMemcpy hinit (fun _ _ _ => Iff.rfl)

/-- Closed `[LibsignalFullPlacement]` 4K/`Ext` SPQR V1 `initialize_bob_session` success at
`InitializeBobV1OptFieldsEnv P F` on `stageP1ProgPlaced ext` (`sessionMemcpyRegionBudgetSpec`). -/
theorem initializeBobSession_ok_v1_4k_full_placed_on_stageP1 [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_on_stageP1 hWF hP hH hMemcpy hinit)

theorem initializeBobSession_ok_v1_4k_full_placed_on_stageP1_of_frozenInit [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_on_stageP1_of_frozenInit hWF hP hH hMemcpy hinit)

theorem initializeBobSession_ok_v1_full_placed_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlacedOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  initializeBobSession_ok_v1_full_placed_of_env_on_stageP1_std
    hWF hP hH hMemcpy hinit (fun _ _ _ => Iff.rfl)

theorem initializeBobSession_ok_v1_4k_full_placed_on_stageP1_std [LibsignalFullPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hH : PqxdhPlacedHookContracts M P C A lim ext)
    (hMemcpy : HookSat ext lsMemcpySym allocMemcpyVmSpec)
    (hinit : InitialStateMemInvPlacedOk M (LibsignalCodeRoLoaded lsmpl) A lim F ext) :
    InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F (InitializeBobV1OptFieldsEnv P F) ext :=
  p2_initBobV1FrozenPlacedOfEnv_to_4K
    (initializeBobSession_ok_v1_full_placed_on_stageP1_std hWF hP hH hMemcpy hinit)

/-- Construct `StageP2BaseCalleesPlaced4K` directly on `stageP1ProgPlaced ext` under
`[LibsignalPlacement]` with zero Block `79` (`Pqxdh::accept`) or Block `327` (`spqr::initial_state`)
seams. -/
theorem StageP2BaseCalleesPlaced4K.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (hAlloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hDealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMemcpy4K : HookSat ext lsMemcpySym p2Memcpy4KSpec)
    (hSame : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpecExt A.repAlloc uuidTryParse))) :
    StageP2BaseCalleesPlaced4K A lim ext where
  publicKeySerialize := p2_publicKeySerialize_of_hooks_placed hShim hAlloc
  promoteMatchingSessionEmpty := promote_matching_session_empty_placed_ok_at
  curveKeyPairSerde := curveKeyPairSerde_placed_ok_at
  kemKeyPairSerde := kemKeyPairSerde_4k_placed_ok_at hShim hAlloc hMemcpy4K
  preKeyRecordKeyPair := preKeyRecordKeyPair_placed_ok_at
  dropSpe2 := drop_spe2_placed_ok_on_stageP1 hDealloc
  isSameAccount := hSame
  promoteStateEmpty := promote_state_empty_4k_placed_ok_at hMemcpy4K
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_placed_ok
  dropSessionStructure3 := drop_session_structure3_placed_ok_on_stageP1 hDealloc

abbrev stageP2BaseCalleesPlaced4K_of_hooks := @StageP2BaseCalleesPlaced4K.of_hooks

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
