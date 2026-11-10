/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudget
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState

/-!
# Budget-Threaded Relocatable Contract Wiring & Composition for `spqr::recv`

Envelope-parametric and default `SpqrRecvEnv` contract assembly (`SpqrRecvPlacedContractsOfEnv`),
relocatable budget specifications (`spqrRecvPlacedSpecXTOfEnv`), and top-level tail composition
for `spqr::recv` (Block `329`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPC_363 blkPC_364 blkPC_365 blkPC_366 blkPC_368 blkPl_363
   blkPl_364 blkPl_365 blkPl_366 blkPl_368 libsignalSessionLib lsLogFilterAddr lsmpl lsρ
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (MlKem MsgPreamble SpqrRecvModel V1State msgPreamble recvResultExactKeyAt spqrAuthApi
   spqrHkdfWith spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded VecArg framelessMemcpySpec spqrRecvStack withLsCodeRoLoaded)
open CryptoVerification.SpqrV1 (ls_subroutine_ok_of_blockProgram_cro)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (subroutine_ok_withLsCallInv_of_plain withLsCallInv)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (blkPC_426 blkPl_426)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap optProtoInnerStateAt_canonical_eq_drop)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_323 blkPl_323)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS ls_subroutine_ok_callInv_of_callInv ls_subroutine_ok_cro_of_callInv
   ls_subroutine_ok_cro_of_cl ls_subroutine_ok_cro_of_cro ls_subroutine_ok_cro_of_plain
   lsro_ctLabelPlacedAt lsro_optProtoInnerStateJumpTablePlacedAt lsro_spqrRecvRoPlacedAt
   lsro_statesFromPbJumpTablePlacedAt lsro_statesIntoPbJumpTablePlacedAt
   lsro_statesRecvJumpTablePlacedAt lsro_v1StateJumpTablesPlacedAt spqrRecvPlacedEntry
   spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvRoPlacedAt_restore)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (chainNewSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (chainRecvKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
  (dropOptProtoSpqrChainSpec dropProtoEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
  (dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.States2Budget (dropChunkedStatesLocal2PlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecPlacedOkExt pqRatchetStateEncodeToVecSpecX)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (withLsRoLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
  (StatesFromPbPlacedOkXOfEnv StatesPlacedSeams StatesPlacedSeamsOfEnv StatesRecvPlacedOkXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlacedBudget
  (chainFrom_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStatePlacedOkOfEnv DecodeStatePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv InitInnerPlacedOkX SpqrBoundedEvs StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
  (MessageDeserializePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv StatesRecvEnv
   initInnerPlacedSpecXOfEnv statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvBudgetPanicPost spqrRecvPlacedCorePostOfEnv spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget (SpqrRecvDropContractsBudget)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4PlacedBudget (step_prologue_to_312_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudget
  (step_decode_and_dispatch_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5PlacedBudgetAux
  (InitInnerPlacedTail InitInnerPlacedTailGen V0ChainPlacedTail V0ChainPlacedTailGen
   V1RatchetPlacedTailLS V1RatchetPlacedTailLSGen)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Re-Exports of `.rodata` Scaffolding and Cross-Block Transfer Combinators -/

export CryptoVerification.SpqrV1.Top.Recv
  (lsro_optProtoInnerStateJumpTablePlacedAt lsro_v1StateJumpTablesPlacedAt
   lsro_statesFromPbJumpTablePlacedAt lsro_statesRecvJumpTablePlacedAt lsro_ctLabelPlacedAt
   lsro_statesIntoPbJumpTablePlacedAt lsro_spqrRecvRoPlacedAt spqrRecvRoPlacedAt_restore
   ls_subroutine_ok_cro_of_cro ls_subroutine_ok_cro_of_cl ls_subroutine_ok_cro_of_callInv
   ls_subroutine_ok_cro_of_plain ls_subroutine_ok_callInv_of_callInv)

/-! ## 2. Contract Bundle Projections & Callee Contract Predicates -/

theorem toDropContractsBudget {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext) :
    SpqrRecvDropContractsBudget A lim F ext where
  dealloc_ok := hC.dealloc_ok
  dropEpochSlice_ok := hC.dropEpochSlice_ok
  dropOptProtoInnerState_ok := hC.dropOptProtoInnerState_ok
  dropOptProtoChain_ok := hC.dropOptProtoChain_ok
  dropChain_ok := hC.dropChain_ok
  dropPqRatchetState_ok := hC.dropPqRatchetState_ok
  dropStates_ok := hC.dropStates_ok

/-- Conversion of `hC.memcpy_ok` (`framelessMemcpyBudgetSpec`) to
    `TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec`. -/
theorem memcpy_plain {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext) :
    subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy")
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec :=
  subroutine_ok_mono hC.memcpy_ok
    (fun ⟨_, _, _⟩ _ _ hp => hp)
    (fun ⟨_, _, _⟩ _ _ _ hq => by
      dsimp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpySpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.framelessMemcpyBudgetSpec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩)

/-- Envelope-parametric Block `324` (`spqr::init_inner`) placed contract predicate. -/
def InitInnerPlacedOkXOfEnv (MC : AllocCostModel)
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (F : ShaCompress)
    (InitEnv : InitInnerGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext))
    (lsmpl.base 324)
    (withLsCodeLoaded lsmpl
      (LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.initInnerPlacedSpecXOfEnv
        MC A lim F InitEnv))

/-- Envelope-parametric Block `334` (`<States>::into_pb`) placed contract predicate on
    `blkPC_334`. -/
def StatesIntoPbPlacedOkXOfEnv (MC : AllocCostModel)
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (F : ShaCompress)
    (IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
    (blkPl_334).base
    (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv MC A lim F IntoPbEnv))

abbrev StatesIntoPbPlacedOkX (MC : AllocCostModel)
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  StatesIntoPbPlacedOkXOfEnv MC A lim F StatesIntoPbEnv ext

/-- Convert a `libsignalSessionLib.blockProgram lsmpl 334` contract into
    `StatesIntoPbPlacedOkXOfEnv`. -/
theorem statesIntoPbPlacedOkXOfEnv_of_blockProgram {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {F : ShaCompress}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv MC A lim F IntoPbEnv))) :
    StatesIntoPbPlacedOkXOfEnv MC A lim F IntoPbEnv ext := by
  unfold StatesIntoPbPlacedOkXOfEnv
  have hprog : (blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext) =
      libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext) :=
    (inferInstance : IsLsBlockProg
      ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      334 (Rust.withPanics ext)).eq_blockProgram
  have hbase : (blkPl_334).base = lsmpl.base 334 := rfl
  rwa [hprog, hbase]

/-! ## 3. Constructing `SpqrRecvPlacedContractsOfEnv` & `SpqrRecvPlacedContracts` -/

/-- Assemble `SpqrRecvPlacedContractsOfEnv canonicalV1InnerHeap A lim F K ... ext` directly from
    placed callee contracts (taking `StatesFromPbPlacedOkXOfEnv` and `StatesRecvPlacedOkXOfEnv`
    directly without requiring send-chunk seams). -/
theorem spqrRecvPlacedContractsOfEnv_of_callees
    {MC : AllocCostModel} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec MC A lim))
    (hmemcpy : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hDropEpochSlice : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec MC A lim)))
    (hDropOptProtoInnerState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec MC A lim)))
    (hDropOptProtoChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec MC A lim)))
    (hDropChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (dropSpqrChainSpec MC A lim)))
    (hDropPqRatchetState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec MC A lim)))
    (hDropStates : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec MC A lim F)))
    (hDecodeState : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim DecodePreEnv DecodePostEnv ext)
    (hInitInner : InitInnerPlacedOkXOfEnv MC A lim F InitEnv ext)
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (blkPl_364).base (chainFromPbSpecX MC A lim))
    (hChainNew : subroutine_ok ((blkPC_363).rebase (blkPl_363).base (Rust.withPanics ext))
      (blkPl_363).base (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) MC A lim)))
    (hChainAddEpoch : subroutine_ok ((blkPC_368).rebase (blkPl_368).base (Rust.withPanics ext))
      (blkPl_368).base (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith F) MC A lim)))
    (hChainRecvKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base (Rust.withPanics ext))
      (blkPl_366).base (withLsCallInv lsmpl (chainRecvKeySpecX MC A lim (spqrHkdfWith F))))
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (blkPl_365).base (chainIntoPbSpecX MC A lim))
    (hMsgDeser : MessageDeserializePlacedOkX spqrPolyApi MC A lim ext)
    (hStatesFromPb : StatesFromPbPlacedOkXOfEnv MC A lim F ext FromPbEnv)
    (hStatesRecv : StatesRecvPlacedOkXOfEnv MC A lim F K ext RecvEnv)
    (hStatesIntoPb : StatesIntoPbPlacedOkXOfEnv MC A lim F IntoPbEnv ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext) :
    SpqrRecvPlacedContractsOfEnv canonicalV1InnerHeap A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext where
  dealloc_ok := hdealloc
  memcpy_ok := hmemcpy
  dropEpochSlice_ok := hDropEpochSlice
  dropOptProtoInnerState_ok := hDropOptProtoInnerState
  dropOptProtoChain_ok := hDropOptProtoChain
  dropChain_ok := hDropChain
  dropPqRatchetState_ok := hDropPqRatchetState
  dropStates_ok := hDropStates
  decodeState_ok := ls_subroutine_ok_cro_of_cro hDecodeState
  initInner_ok := by
    have hinit_cro : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 324 (Rust.withPanics ext))
        (lsmpl.base 324) (withLsCodeRoLoaded lsmpl (initInnerPlacedSpecXOfEnv MC A lim F InitEnv)) :=
      subroutine_ok_mono hInitInner
        (fun _ _ _ hpre => by
          dsimp only [withLsCodeRoLoaded,
            CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
            withLsCodeLoaded, initInnerPlacedSpecXOfEnv,
            LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.initInnerPlacedSpecXOfEnv,
            LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget.initInnerPlacedSpecOfEnv] at hpre ⊢
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
          exact ⟨hpre.1.1, hpre.2⟩)
        (fun _ _ _ _ hpost => hpost)
    exact ls_subroutine_ok_of_blockProgram_cro hinit_cro
  chainFrom_ok := by
    have h_fpb_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
        (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX MC A lim)) :=
      ls_subroutine_ok_callInv_of_callInv (subroutine_ok_withLsCallInv_of_plain hChainFromPb)
    have h_new_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
        (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) MC A lim)) :=
      ls_subroutine_ok_callInv_of_callInv hChainNew
    exact ls_subroutine_ok_cro_of_callInv (chainFrom_placed_ok_of_contracts_x h_fpb_323 h_new_323)
  chainFromPb_ok := ls_subroutine_ok_cro_of_plain hChainFromPb
  chainNew_ok := ls_subroutine_ok_cro_of_callInv hChainNew
  chainAddEpoch_ok := ls_subroutine_ok_cro_of_callInv hChainAddEpoch
  chainRecvKey_ok := ls_subroutine_ok_cro_of_callInv hChainRecvKey
  chainIntoPb_ok := ls_subroutine_ok_cro_of_plain hChainIntoPb
  messageDeserialize_ok := ls_subroutine_ok_cro_of_callInv hMsgDeser
  statesFromPb_ok := ls_subroutine_ok_of_blockProgram_cro hStatesFromPb
  statesRecv_ok := ls_subroutine_ok_of_blockProgram_cro hStatesRecv
  statesIntoPb_ok := ls_subroutine_ok_cro_of_cl hStatesIntoPb
  encodeToVec_ok := by
    have henc_cro : subroutine_ok ((blkPC_426).rebase (blkPl_426).base (Rust.withPanics ext))
        (blkPl_426).base (withLsCodeRoLoaded lsmpl (pqRatchetStateEncodeToVecSpecX A lim)) :=
      subroutine_ok_mono hEncodeToVec
        (fun _ _ _ hpre => by
          dsimp only [withLsCodeRoLoaded,
            CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
            withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecSpecX] at hpre ⊢
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
          refine ⟨hpre.1.2, ?_⟩
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
          exact ⟨hpre.1.1, hpre.2⟩)
        (fun _ _ _ _ hpost => hpost)
    exact ls_subroutine_ok_cro_of_cro henc_cro
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A.repAlloc

/-- Assemble `SpqrRecvPlacedContractsOfEnv canonicalV1InnerHeap A lim F K ... ext` from placed
    callee contracts and `StatesPlacedSeamsOfEnv`. -/
theorem spqrRecvPlacedContractsOfEnv_of_okX
    {MC : AllocCostModel} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {HsEkEnv : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
    {Ct1rEkEnv : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    {Ct1sEnv : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {EkCt1sEnv : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {Ct2sEnv : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec MC A lim))
    (hmemcpy : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hDropEpochSlice : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec MC A lim)))
    (hDropOptProtoInnerState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec MC A lim)))
    (hDropOptProtoChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec MC A lim)))
    (hDropChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (dropSpqrChainSpec MC A lim)))
    (hDropPqRatchetState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec MC A lim)))
    (hDropStates : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec MC A lim F)))
    (hDecodeState : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim DecodePreEnv DecodePostEnv ext)
    (hInitInner : InitInnerPlacedOkXOfEnv MC A lim F InitEnv ext)
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (blkPl_364).base (chainFromPbSpecX MC A lim))
    (hChainNew : subroutine_ok ((blkPC_363).rebase (blkPl_363).base (Rust.withPanics ext))
      (blkPl_363).base (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) MC A lim)))
    (hChainAddEpoch : subroutine_ok ((blkPC_368).rebase (blkPl_368).base (Rust.withPanics ext))
      (blkPl_368).base (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith F) MC A lim)))
    (hChainRecvKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base (Rust.withPanics ext))
      (blkPl_366).base (withLsCallInv lsmpl (chainRecvKeySpecX MC A lim (spqrHkdfWith F))))
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (blkPl_365).base (chainIntoPbSpecX MC A lim))
    (hMsgDeser : MessageDeserializePlacedOkX spqrPolyApi MC A lim ext)
    (hStatesIntoPb : StatesIntoPbPlacedOkXOfEnv MC A lim F IntoPbEnv ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hSeams : StatesPlacedSeamsOfEnv MC A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext) :
    SpqrRecvPlacedContractsOfEnv canonicalV1InnerHeap A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext :=
  spqrRecvPlacedContractsOfEnv_of_callees hdealloc hmemcpy
    hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
    hDropPqRatchetState hDropStates
    hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
    hMsgDeser hSeams.statesFromPb_ok hSeams.statesRecv_ok hStatesIntoPb hEncodeToVec

theorem spqrRecvPlacedContracts_of_okX
    {MC : AllocCostModel} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec MC A lim))
    (hmemcpy : subroutine_ok (spqrRecvPlacedProg ext)
      (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (hDropEpochSlice : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec MC A lim)))
    (hDropOptProtoInnerState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 267) (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec MC A lim)))
    (hDropOptProtoChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 266) (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec MC A lim)))
    (hDropChain : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 269) (withLsCodeLoaded lsmpl (dropSpqrChainSpec MC A lim)))
    (hDropPqRatchetState : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 270) (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec MC A lim)))
    (hDropStates : subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 273) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec MC A lim F)))
    (hDecodeState : DecodeStatePlacedOkX canonicalV1InnerHeap A lim ext)
    (hInitInner : InitInnerPlacedOkX MC A lim F ext)
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (blkPl_364).base (chainFromPbSpecX MC A lim))
    (hChainNew : subroutine_ok ((blkPC_363).rebase (blkPl_363).base (Rust.withPanics ext))
      (blkPl_363).base (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith F) MC A lim)))
    (hChainAddEpoch : subroutine_ok ((blkPC_368).rebase (blkPl_368).base (Rust.withPanics ext))
      (blkPl_368).base (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith F) MC A lim)))
    (hChainRecvKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base (Rust.withPanics ext))
      (blkPl_366).base (withLsCallInv lsmpl (chainRecvKeySpecX MC A lim (spqrHkdfWith F))))
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (blkPl_365).base (chainIntoPbSpecX MC A lim))
    (hMsgDeser : MessageDeserializePlacedOkX spqrPolyApi MC A lim ext)
    (hStatesIntoPb : StatesIntoPbPlacedOkX MC A lim F ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hSeams : StatesPlacedSeams MC A lim F K ext) :
    SpqrRecvPlacedContracts canonicalV1InnerHeap A lim F K ext :=
  spqrRecvPlacedContractsOfEnv_of_okX hdealloc hmemcpy
    hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
    hDropPqRatchetState hDropStates
    hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
    hMsgDeser hStatesIntoPb hEncodeToVec hSeams

/-! ## 4. Relocatable Budget Top-Level `spqr::recv` Specifications & Composition from Tails -/

/-- Envelope-parametric relocatable raw budget specification of `spqr::recv` (`Block 329`) with
    `recvResultExactKeyAt` (without `withLsCodeRoLoaded`). -/
def spqrRecvPlacedRawSpecXOfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel)
    (Env : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) where
  pre := fun ((st, msg, ret), st_cost) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret ∧
      FitsEnv MC lim st_cost (Env st msg)⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st_cost s ∗ stackAt s.sp spqrRecvStack
  post := fun ((st, msg, ret), st_cost) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env st msg evs ∧ ¬ M.recvPanics st.bytes msg.bytes⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim (MC.stepEvents evs st_cost) sf ∗ stackAt s0.sp spqrRecvStack
  onPanic := fun ((st, msg, _), _) s0 sf =>
    ⌜M.recvPanics st.bytes msg.bytes ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Envelope-parametric relocatable budget specification of `spqr::recv` (`Block 329`) with
    `withLsCodeRoLoaded lsmpl`. -/
def spqrRecvPlacedSpecXOfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel)
    (Env : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  withLsCodeRoLoaded lsmpl (spqrRecvPlacedRawSpecXOfEnv A lim M Env)

/-- Envelope-parametric relocatable raw budget specification of `spqr::recv` (`Block 329`)
    enriched with `tokenInitPlacedAt` and input/stack bounds (`st.bytes.length < 2 ^ 32 ∧
    msg.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat`). -/
def spqrRecvPlacedRawSpecXTOfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel)
    (Env : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  { spqrRecvPlacedRawSpecXOfEnv A lim M Env with
    pre := fun x s =>
      ⌜x.1.1.bytes.length < 2 ^ 32 ∧ x.1.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗ (spqrRecvPlacedRawSpecXOfEnv A lim M Env).pre x s
    post := fun x s0 sf =>
      tokenInitPlacedAt ∗ (spqrRecvPlacedRawSpecXOfEnv A lim M Env).post x s0 sf }

/-- Envelope-parametric relocatable budget specification of `spqr::recv` (`Block 329`) enriched
    with `tokenInitPlacedAt`, input/stack bounds, and `withLsCodeRoLoaded lsmpl`. -/
def spqrRecvPlacedSpecXTOfEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel)
    (Env : VecArg → VecArg → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  { spqrRecvPlacedSpecXOfEnv A lim M Env with
    pre := fun x s =>
      ⌜x.1.1.bytes.length < 2 ^ 32 ∧ x.1.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗ (spqrRecvPlacedSpecXOfEnv A lim M Env).pre x s
    post := fun x s0 sf =>
      tokenInitPlacedAt ∗ (spqrRecvPlacedSpecXOfEnv A lim M Env).post x s0 sf }

abbrev spqrRecvPlacedRawSpecX {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  spqrRecvPlacedRawSpecXOfEnv A lim M SpqrRecvEnv

abbrev spqrRecvPlacedSpecX {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  spqrRecvPlacedSpecXOfEnv A lim M SpqrRecvEnv

abbrev spqrRecvPlacedRawSpecXT {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  spqrRecvPlacedRawSpecXTOfEnv A lim M SpqrRecvEnv

abbrev spqrRecvPlacedSpecXT {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (M : SpqrRecvModel) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  spqrRecvPlacedSpecXTOfEnv A lim M SpqrRecvEnv

/-- Envelope-parametric `SepWPpLS` execution of `spqr::recv` (`Block 329`) from entry to
    `s0.readReg64 .x30` combining `step_prologue_to_312_placed_ofEnv`
    (`Part4PlacedBudget.lean`), `step_decode_and_dispatch_placed_ofEnv`
    (`Part5PlacedBudget.lean`), and the 3 version-branch tail contracts (`V0ChainPlacedTailGen`,
    `InitInnerPlacedTailGen`, `V1RatchetPlacedTailLSGen`). -/
theorem spqrRecv_placed_sepWPpLS_of_tails_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred)
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (Env : List AllocEvent → Prop)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hnil : Env [])
    (hFit_dec : ∀ pre : MsgPreamble, msgPreamble msg.bytes = .ok pre →
      FitsEnv MC lim st_cost (DecodePreEnv ⟨st, s0.sp - 3056#64⟩))
    (hEnv_dec : ∀ pre : MsgPreamble, msgPreamble msg.bytes = .ok pre →
      ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        ∀ evs_d, FreeOnlyEvs evs_d → Env (evs_dec ++ evs_d))
    (hv0 : ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      V0ChainPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hinit : ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      InitInnerPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hv1 : ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
      V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R) R)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cost s0 ∗
      stackAt s0.sp spqrRecvStack) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_prologue_to_312_placed_ofEnv A lim st_cost Env hnil F K ext st msg ret s0 P R
    hpc hrun hsp_align hx0 hx1 hx8 hP
    (fun pre msgPtr s1 P1 hpre hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1 =>
      step_decode_and_dispatch_placed_ofEnv H_inner A lim st_cost DecodePreEnv DecodePostEnv Env
        F K ext (toDropContractsBudget hC) (memcpy_plain hC) hC.h_inner_eq hC.decodeState_ok
        st msg ret pre msgPtr hst_len hpre hvalid s0 s1 P1 R
        (hFit_dec pre hpre) (hEnv_dec pre hpre) hv0 hinit hv1 hsp_align
        hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1)

/-- Envelope-parametric `subroutine_ok` proof that `spqr::recv` (`Block 329`) satisfies
    `spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env` on `spqrRecvPlacedProg ext` given
    `SpqrRecvPlacedContractsOfEnv` and the 3 version-branch tail contracts. -/
theorem spqrRecv_placed_ok_of_tails_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred)
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (Env : VecArg → VecArg → List AllocEvent → Prop)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (hnil : ∀ (st msg : VecArg), st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      (∃ st_cost : MC.σ, FitsEnv MC lim st_cost (Env st msg)) → Env st msg [])
    (hFit_dec : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ)
      (pre : MsgPreamble),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      msgPreamble msg.bytes = .ok pre →
      FitsEnv MC lim st_cost (DecodePreEnv ⟨st, s0.sp - 3056#64⟩))
    (hEnv_dec : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ)
      (pre : MsgPreamble),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      msgPreamble msg.bytes = .ok pre →
      ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        ∀ evs_d, FreeOnlyEvs evs_d → Env st msg (evs_dec ++ evs_d))
    (hv0 : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ) (R : SepProp),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        V0ChainPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
          (spqrRecvPlacedPostOfEnv A lim st_cost (Env st msg) (spqrV1Recv F K) st msg ret s0 R) R)
    (hinit : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ) (R : SepProp),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        InitInnerPlacedTailGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
          (spqrRecvPlacedPostOfEnv A lim st_cost (Env st msg) (spqrV1Recv F K) st msg ret s0 R) R)
    (hv1 : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ) (R : SepProp),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      ∀ evs_dec, DecodePostEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        V1RatchetPlacedTailLSGen A lim (MC.stepEvents evs_dec st_cost) F K ext st msg ret s0
          (spqrRecvPlacedPostOfEnv A lim st_cost (Env st msg) (spqrV1Recv F K) st msg ret s0 R) R) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) := by
  have hok_core : subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      { spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env with
        post := fun ((st, msg, ret), st_cost) s0 sf =>
          spqrRecvPlacedCorePostOfEnv A lim st_cost (Env st msg) (spqrV1Recv F K) st msg ret s0 sf } := by
    apply subroutine_ok_of_sepWPp
    intro ⟨⟨st, msg, ret⟩, st_cost⟩ R s0 hpc hrun hpre hsp_align
    dsimp only [spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv,
      withLsCodeRoLoaded, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      spqrRecvPlacedRawSpecXOfEnv] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hst_len, hmsg_len, hsp_lo⟩, hpre⟩
    have hpre1 :
        s0.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = st.v ∧ s0.readReg64 .x1 = msg.v ∧ s0.readReg64 .x8 = ret ∧
              FitsEnv MC lim st_cost (Env st msg)⌝ ∗
            ((lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗
              (st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
                A.pool lim st_cost s0 ∗ stackAt s0.sp spqrRecvStack ∗ R))) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre1
    rcases hpre1 with ⟨hcrl0, hpre2⟩
    rw [satisfies_pure_sepConj] at hpre2
    rcases hpre2 with ⟨⟨hx0, hx1, hx8, hfit0⟩, hmem0⟩
    have hmem_ro :
        s0.mem ⊨ spqrRecvRoPlacedAt ∗
          (st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
            A.pool lim st_cost s0 ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
      lsro_spqrRecvRoPlacedAt hcrl0.2 hmem0
    let P0 :=
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim st_cost s0 ∗ stackAt s0.sp spqrRecvStack
    have hP0 : s0.mem ⊨ P0 ∗ R :=
      Satisfies.mono (Entails.of_eq (by dsimp only [P0]; ac_rfl)) hmem_ro
    exact ⟨P0, R, hP0,
      spqrRecv_placed_sepWPpLS_of_tails_ofEnv H_inner (Env st msg) hC st msg ret s0 P0 R hst_len
        (hnil st msg hst_len hmsg_len ⟨st_cost, hfit0⟩)
        (fun pre hpre_eq => hFit_dec st msg ret s0 st_cost pre hst_len hmsg_len hsp_align hsp_lo hfit0 hpre_eq)
        (fun pre hpre_eq => hEnv_dec st msg ret s0 st_cost pre hst_len hmsg_len hsp_align hsp_lo hfit0 hpre_eq)
        (hv0 st msg ret s0 st_cost R hst_len hmsg_len hsp_align hsp_lo hfit0)
        (hinit st msg ret s0 st_cost R hst_len hmsg_len hsp_align hsp_lo hfit0)
        (hv1 st msg ret s0 st_cost R hst_len hmsg_len hsp_align hsp_lo hfit0)
        hpc hrun hsp_align hx0 hx1 hx8 rfl hcrl0⟩
  refine subroutine_ok_mono hok_core (fun _ _ _ h => h) ?_
  rintro ⟨⟨st, msg, ret⟩, st_cost⟩ R s0 sf hcore
  dsimp only [spqrRecvPlacedCorePostOfEnv] at hcore
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hcore
  rcases hcore with ⟨evs, hcore⟩
  have hro :
      sf.mem ⊨ spqrRecvRoPlacedAt ∗
        (⌜sf.trace = s0.trace ∧ Env st msg evs ∧ ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes⌝ ∗
          st.at A.repAlloc ∗ msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs st_cost) sf ∗ stackAt s0.sp spqrRecvStack ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hcore
  have hlt := spqrRecvRoPlacedAt_restore hro
  dsimp only [spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv,
    withLsCodeRoLoaded, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
    spqrRecvPlacedRawSpecXOfEnv]
  simp only [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨evs, Satisfies.mono (Entails.of_eq (by ac_rfl)) hlt⟩

theorem spqrRecv_placed_ok_of_tails {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred)
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (hFit_dec : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ)
      (pre : MsgPreamble),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      msgPreamble msg.bytes = .ok pre →
      FitsEnv MC lim st_cost (DecodeStateEnv ⟨st, s0.sp - 3056#64⟩))
    (hEnv_dec : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ)
      (pre : MsgPreamble),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      msgPreamble msg.bytes = .ok pre →
      ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        ∀ evs_d, FreeOnlyEvs evs_d → SpqrRecvEnv st msg (evs_dec ++ evs_d))
    (hv0 : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ) (R : SepProp),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        V0ChainPlacedTail A lim st_cost evs_dec F K ext st msg ret s0 R)
    (hinit : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ) (R : SepProp),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        InitInnerPlacedTail A lim st_cost evs_dec F K ext st msg ret s0 R)
    (hv1 : ∀ (st msg : VecArg) (ret : BitVec 64) (s0 : State) (st_cost : MC.σ) (R : SepProp),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      ∀ evs_dec, DecodeStateEnv ⟨st, s0.sp - 3056#64⟩ evs_dec →
        V1RatchetPlacedTailLS A lim st_cost evs_dec F K ext st msg ret s0 R) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXT A lim (spqrV1Recv F K)) :=
  spqrRecv_placed_ok_of_tails_ofEnv H_inner SpqrRecvEnv hC
    (fun _ _ _ _ _ => SpqrBoundedEvs.nil _ _)
    hFit_dec hEnv_dec hv0 hinit hv1

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
