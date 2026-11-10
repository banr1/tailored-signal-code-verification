/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Program-Side Linked Envelope Witnesses for `spqr::recv` (`Block 329`)

Instantiates `FinalPlacedBudget`'s envelope-parametric `subroutine_ok` contracts for `spqr::recv`
(`Block 329`) at the existentially lifted 12-ghost linked envelopes `SpqrRecvTightLinkedEnv`,
`SpqrRecvC07TightLinkedEnv`, and `SpqrRecvC07C09aTightLinkedEnv`, and bridges them across
`DEV-SPQR2` from `spqrV1Recv F K` to `spqrV1 F K` under `tokenInitPlacedAt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_363 blkPC_364 blkPC_365 blkPC_366 blkPC_368 blkPl_363 blkPl_364
   blkPl_365 blkPl_366 blkPl_368 libsignalSessionLib lsLogFilterAddr lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem States V1State recvResultAtX_entails_recvResultAt spqrAuthApi spqrHkdfWith
   spqrPolyApi spqrV1 spqrV1Recv spqrV1Recv_eq spqrV1_eq)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SpqrModel VecArg logOff spqrRecvResultAt spqrRecvStack
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt
  (logOff_tryDecryptPlacedImg tryDecryptPlacedImg)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (spqrRecvRawSpec)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedEntry spqrRecvPlacedProg)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv SpqrRecvC07TightLinkedEnv SpqrRecvTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
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
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecPlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
  (StatesFromPbPlacedOkXOfEnv StatesPlacedSeamsOfEnv StatesRecvPlacedOkXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStatePlacedOkOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (InitInnerEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
  (MessageDeserializePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (InitInnerPlacedOkXOfEnv StatesIntoPbPlacedOkXOfEnv spqrRecvPlacedRawSpecXOfEnv
   spqrRecvPlacedSpecXOfEnv spqrRecvPlacedSpecXTOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget (SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
  (spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv
   spqr_recv_placed_ok_blockProgram_ofEnv spqr_recv_placed_ok_blockProgram_of_contracts_ofEnv
   spqr_recv_placed_ok_ofEnv spqr_recv_placed_ok_of_callees_ofEnv
   spqr_recv_placed_ok_of_contracts_ofEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.Simp
  (spqrRecvResultAt_atState vecArg_at_atState)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

export LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
  (spqrRecvC07C09aTightLinkedEnv_nil_exists spqrRecvTightLinkedEnv_nil_exists)
export LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitnessAux
  (spqrRecvBranchHyps_c07TightLinked spqrRecvBranchHyps_c07c09aRawTightLinked
   spqrRecvBranchHyps_c07c09aTightLinked spqrRecvBranchHyps_tightLinked)

/-! ## `Block 329` (`spqr::recv`) Witnesses at Linked Envelopes -/

section ProgramWitnesses

variable [LibsignalPlacement]

/-- Linked `subroutine_ok` witness for `spqr::recv` (`Block 329`) on `spqrRecvPlacedProg ext` from `SpqrRecvPlacedContractsOfEnv`.
-/
theorem spqr_recv_placed_ok_of_contracts_tightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodeStateEnv' : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv' : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun g => DecodeStateEnv' g.st.bytes) (fun g => DecodeStateEnv' g.st.bytes)
      (InitInnerEnv F) StatesFromPbEnv' (fun g => StatesRecvEnv' g.self g.msg) StatesIntoPbEnv' ext) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
            StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
            evs)) :=
  spqr_recv_placed_ok_of_contracts_ofEnv
    (fun (st _msg : VecArg) (evs : List AllocEvent) =>
      ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
          StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    hC
    (fun st _ _ _ _ => spqrRecvTightLinkedEnv_nil_exists F K
      DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv' StatesRecvEnv' st.bytes)
    (fun st msg s0 st_cost _ _ _ _ hfit =>
      spqrRecvBranchHyps_tightLinked st msg s0 st_cost
        (fun _ h => h) (fun _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs =>
          hfit evs ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto _ hevs =>
          ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩))

theorem spqr_recv_placed_ok_blockProgram_of_contracts_tightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodeStateEnv' : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv' : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun g => DecodeStateEnv' g.st.bytes) (fun g => DecodeStateEnv' g.st.bytes)
      (InitInnerEnv F) StatesFromPbEnv' (fun g => StatesRecvEnv' g.self g.msg) StatesIntoPbEnv' ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
            StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
            evs)) :=
  spqr_recv_placed_ok_blockProgram_of_contracts_ofEnv
    (fun (st _msg : VecArg) (evs : List AllocEvent) =>
      ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
          StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    hC
    (fun st _ _ _ _ => spqrRecvTightLinkedEnv_nil_exists F K
      DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv' StatesRecvEnv' st.bytes)
    (fun st msg s0 st_cost _ _ _ _ hfit =>
      spqrRecvBranchHyps_tightLinked st msg s0 st_cost
        (fun _ h => h) (fun _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs =>
          hfit evs ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto _ hevs =>
          ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩))

theorem spqr_recv_placed_ok_blockProgram_ext_of_contracts_tightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodeStateEnv' : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv' : V1State → List AllocEvent → Prop}
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun g => DecodeStateEnv' g.st.bytes) (fun g => DecodeStateEnv' g.st.bytes)
      (InitInnerEnv F) StatesFromPbEnv' (fun g => StatesRecvEnv' g.self g.msg) StatesIntoPbEnv' ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 ext)
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
            StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
            evs)) :=
  spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv
    (fun (st _msg : VecArg) (evs : List AllocEvent) =>
      ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvTightLinkedEnv F K DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv'
          StatesRecvEnv' st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    hp hC
    (fun st _ _ _ _ => spqrRecvTightLinkedEnv_nil_exists F K
      DecodeStateEnv' StatesFromPbEnv' StatesIntoPbEnv' StatesRecvEnv' st.bytes)
    (fun st msg s0 st_cost _ _ _ _ hfit =>
      spqrRecvBranchHyps_tightLinked st msg s0 st_cost
        (fun _ h => h) (fun _ h => h) (fun _ _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs =>
          hfit evs ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto _ hevs =>
          ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩))

/-- Codec-instantiated `subroutine_ok` witness for `spqr::recv` at the existentially lifted `SpqrRecvC07TightLinkedEnv`.
-/
theorem spqr_recv_placed_ok_of_contracts_c07TightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvEnv' g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_of_contracts_tightLinked hC

theorem spqr_recv_placed_ok_blockProgram_of_contracts_c07TightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvEnv' g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_blockProgram_of_contracts_tightLinked hC

theorem spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07TightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvEnv' g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 ext)
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_blockProgram_ext_of_contracts_tightLinked hp hC

/-- Callee-contract variant of `spqr_recv_placed_ok_of_contracts_c07TightLinked` taking `StatesFromPbPlacedOkXOfEnv` and `StatesRecvPlacedOkXOfEnv` directly.
-/
theorem spqr_recv_placed_ok_of_callees_c07TightLinked {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
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
    (hDecodeState : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv) ext)
    (hInitInner : InitInnerPlacedOkXOfEnv MC A lim F (InitInnerEnv F) ext)
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
    (hStatesFromPb : StatesFromPbPlacedOkXOfEnv MC A lim F ext (fun _ => StatesFromPbTightEnv))
    (hStatesRecv : StatesRecvPlacedOkXOfEnv MC A lim F K ext (fun g => StatesRecvEnv' g.self g.msg))
    (hStatesIntoPb : StatesIntoPbPlacedOkXOfEnv MC A lim F (fun _ => StatesIntoPbTightEnv) ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_of_callees_ofEnv
    (fun (st _msg : VecArg) (evs : List AllocEvent) =>
      ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    hdealloc hmemcpy hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
    hDropPqRatchetState hDropStates hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch
    hChainRecvKey hChainIntoPb hMsgDeser hStatesFromPb hStatesRecv hStatesIntoPb hEncodeToVec
    (fun st _ _ _ _ => spqrRecvTightLinkedEnv_nil_exists F K
      (fun _ => DecodeStateTightEnv) (fun _ => StatesFromPbTightEnv)
      (fun _ => StatesIntoPbTightEnv) StatesRecvEnv' st.bytes)
    (fun st msg s0 st_cost _ _ _ _ hfit =>
      spqrRecvBranchHyps_c07TightLinked st msg s0 st_cost
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs =>
          hfit evs ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto _ hevs =>
          ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩))

/-- Seam-bundle (`StatesPlacedSeamsOfEnv`) variant of `spqr_recv_placed_ok_of_contracts_c07TightLinked`.
-/
theorem spqr_recv_placed_ok_c07TightLinked {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
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
    (hDecodeState : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv) ext)
    (hInitInner : InitInnerPlacedOkXOfEnv MC A lim F (InitInnerEnv F) ext)
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
    (hStatesIntoPb : StatesIntoPbPlacedOkXOfEnv MC A lim F (fun _ => StatesIntoPbTightEnv) ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hSeams : StatesPlacedSeamsOfEnv MC A lim F K
      (fun _ => StatesFromPbTightEnv) (fun g => StatesRecvEnv' g.self g.msg)
      HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_ofEnv
    (fun (st _msg : VecArg) (evs : List AllocEvent) =>
      ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    hdealloc hmemcpy hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
    hDropPqRatchetState hDropStates hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch
    hChainRecvKey hChainIntoPb hMsgDeser hStatesIntoPb hEncodeToVec hSeams
    (fun st _ _ _ _ => spqrRecvTightLinkedEnv_nil_exists F K
      (fun _ => DecodeStateTightEnv) (fun _ => StatesFromPbTightEnv)
      (fun _ => StatesIntoPbTightEnv) StatesRecvEnv' st.bytes)
    (fun st msg s0 st_cost _ _ _ _ hfit =>
      spqrRecvBranchHyps_c07TightLinked st msg s0 st_cost
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs =>
          hfit evs ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto _ hevs =>
          ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩))

theorem spqr_recv_placed_ok_blockProgram_c07TightLinked {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
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
    (hDecodeState : DecodeStatePlacedOkOfEnv canonicalV1InnerHeap A lim
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv) ext)
    (hInitInner : InitInnerPlacedOkXOfEnv MC A lim F (InitInnerEnv F) ext)
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
    (hStatesIntoPb : StatesIntoPbPlacedOkXOfEnv MC A lim F (fun _ => StatesIntoPbTightEnv) ext)
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hSeams : StatesPlacedSeamsOfEnv MC A lim F K
      (fun _ => StatesFromPbTightEnv) (fun g => StatesRecvEnv' g.self g.msg)
      HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_blockProgram_ofEnv
    (fun (st _msg : VecArg) (evs : List AllocEvent) =>
      ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    hdealloc hmemcpy hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
    hDropPqRatchetState hDropStates hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch
    hChainRecvKey hChainIntoPb hMsgDeser hStatesIntoPb hEncodeToVec hSeams
    (fun st _ _ _ _ => spqrRecvTightLinkedEnv_nil_exists F K
      (fun _ => DecodeStateTightEnv) (fun _ => StatesFromPbTightEnv)
      (fun _ => StatesIntoPbTightEnv) StatesRecvEnv' st.bytes)
    (fun st msg s0 st_cost _ _ _ _ hfit =>
      spqrRecvBranchHyps_c07TightLinked st msg s0 st_cost
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs hevs =>
          hfit evs ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩)
        (fun pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto _ hevs =>
          ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, hevs⟩))

/-- Closed `SpqrRecvC07C09aTightLinkedEnv` `subroutine_ok` witness for `spqr::recv` on `blockProgram lsmpl 329 (Rust.withPanics ext)`.
-/
theorem spqr_recv_placed_ok_blockProgram_of_contracts_c07c09aTightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07C09aTightLinkedEnv F K
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_blockProgram_of_contracts_c07TightLinked hC

theorem spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07c09aTightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 ext)
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07C09aTightLinkedEnv F K
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_blockProgram_ext_of_contracts_c07TightLinked hp hC

theorem spqr_recv_placed_ok_blockProgram_of_contracts_c07c09aRawTightLinked {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec.StatesRecvEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)
        (fun st _msg evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K
            LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec.StatesRecvEnv
            st.bytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_placed_ok_blockProgram_of_contracts_c07TightLinked hC

/-! ## `DEV-SPQR2` `tokenInitPlacedAt`-Framed Spec Bridges -/

/-- `tokenInitPlacedAt`-framed relocatable `spqr::recv` budget spec matching `KeyDeriveBaseBudget.spqrRecvRawSpecPlaced`.
-/
def spqrRecvKeyDeriveRawSpecPlacedWT {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (S : SpqrModel)
    (RcvPred : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  { LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced
      A lim S RcvPred with
    pre := fun x s =>
      ⌜x.1.1.bytes.length < 2 ^ 32 ∧ x.1.2.1.bytes.length < 2 ^ 40 ∧
        spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced
          A lim S RcvPred).pre x s
    post := fun x s0 sf =>
      tokenInitPlacedAt ∗
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced
          A lim S RcvPred).post x s0 sf }

def spqrRecvKeyDeriveSpecPlacedWT {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (S : SpqrModel)
    (RcvPred : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  withLsCodeRoLoaded lsmpl (spqrRecvKeyDeriveRawSpecPlacedWT A lim S RcvPred)

/-- `tokenInitPlacedAt`-framed relocatable `spqr::recv` budget spec matching `PqRecvBudgetDefs.spqrRecvRawSpecPlaced`.
-/
def spqrRecvPqRawSpecPlacedWT {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (S : SpqrModel)
    (RcvPred : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  { LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.spqrRecvRawSpecPlaced
      A lim S RcvPred with
    pre := fun x s =>
      ⌜x.1.1.bytes.length < 2 ^ 32 ∧ x.1.2.1.bytes.length < 2 ^ 40 ∧
        spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.spqrRecvRawSpecPlaced
          A lim S RcvPred).pre x s
    post := fun x s0 sf =>
      tokenInitPlacedAt ∗
        (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.spqrRecvRawSpecPlaced
          A lim S RcvPred).post x s0 sf }

def spqrRecvPqSpecPlacedWT {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (S : SpqrModel)
    (RcvPred : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × MC.σ) :=
  withLsCodeRoLoaded lsmpl (spqrRecvPqRawSpecPlacedWT A lim S RcvPred)

/-- `DEV-SPQR2` budget bridge from `spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K)` to `spqrRecvKeyDeriveSpecPlacedWT A lim (spqrV1 F K)`.
-/
theorem spqrRecvKeyDeriveSpecPlacedWT_ok_of_v1 {MC : AllocCostModel}
    {prog : Program} {entry_pc : BitVec 64}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (F : ShaCompress) (K : MlKem)
    (RcvPred : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (hRecvV1 : subroutine_ok prog entry_pc
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) (fun st msg => RcvPred st.bytes msg.bytes))) :
    subroutine_ok prog entry_pc
      (spqrRecvKeyDeriveSpecPlacedWT A lim (spqrV1 F K) RcvPred) := by
  have hpan_eq : (spqrV1Recv F K).recvPanics = fun st msg => (spqrV1 F K).recvPanics st msg = true := by
    rw [spqrV1Recv_eq, spqrV1_eq]; rfl
  refine subroutine_ok_mono hRecvV1
    (fun ((st, msg, ret), st_cost) R s0 hpre => by
      dsimp only [spqrRecvKeyDeriveSpecPlacedWT, spqrRecvKeyDeriveRawSpecPlacedWT,
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv, spqrRecvPlacedRawSpecXOfEnv,
        withLsCodeRoLoaded] at hpre ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      rw [logOff_tryDecryptPlacedImg]
      exact Entails.of_eq (by sep_ac_rfl))
    (fun ((st, msg, ret), st_cost) R s0 sf hpost => by
      dsimp only [spqrRecvKeyDeriveSpecPlacedWT, spqrRecvKeyDeriveRawSpecPlacedWT,
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv, spqrRecvPlacedRawSpecXOfEnv,
        withLsCodeRoLoaded] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      rw [logOff_tryDecryptPlacedImg]
      refine sepConj_mono_right (Entails.sepExists_mono fun evs => ?_)
      apply Entails.pure_left
      rintro ⟨htr, hevs, hnp⟩
      rw [hpan_eq] at hnp
      refine Entails.pure_right ⟨htr, hnp, hevs⟩ ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (recvResultAtX_entails_recvResultAt A.repAlloc ret F K st.bytes msg.bytes))))
    (fun ((st, msg, _), _) R s0 sf hpan => by
      dsimp only [spqrRecvKeyDeriveSpecPlacedWT, spqrRecvKeyDeriveRawSpecPlacedWT,
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced,
        spqrRecvPlacedSpecXTOfEnv, spqrRecvPlacedSpecXOfEnv, spqrRecvPlacedRawSpecXOfEnv,
        withLsCodeRoLoaded] at hpan ⊢
      rwa [hpan_eq] at hpan)
    (fun _ _ _ _ _ he => he)

theorem spqrRecvPqSpecPlacedWT_ok_of_keyDeriveWT {MC : AllocCostModel}
    {prog : Program} {entry_pc : BitVec 64}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (S : SpqrModel)
    (RcvPred : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (hKD : subroutine_ok prog entry_pc (spqrRecvKeyDeriveSpecPlacedWT A lim S RcvPred)) :
    subroutine_ok prog entry_pc (spqrRecvPqSpecPlacedWT A lim S RcvPred) := by
  refine subroutine_ok_mono hKD
    (fun ((st, msg, ret), st_cost) R s0 hpre => by
      dsimp only [spqrRecvPqSpecPlacedWT, spqrRecvPqRawSpecPlacedWT,
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.spqrRecvRawSpecPlaced,
        spqrRecvRawSpec, spqrRecvKeyDeriveSpecPlacedWT, spqrRecvKeyDeriveRawSpecPlacedWT,
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced,
        withLsCodeRoLoaded] at hpre ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpre
      simp only [vecArg_at_atState, RustCliAllocBudget.atState_pool]
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ?_))
      apply Entails.pure_left; intro hfit
      apply Entails.pure_left; rintro ⟨hx0, hx1, hx8⟩
      exact Entails.pure_right ⟨hx0, hx1, hx8, hfit⟩ (Entails.refl _))
    (fun ((st, msg, ret), st_cost) R s0 sf hpost => by
      dsimp only [spqrRecvPqSpecPlacedWT, spqrRecvPqRawSpecPlacedWT,
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.spqrRecvRawSpecPlaced,
        spqrRecvRawSpec, spqrRecvKeyDeriveSpecPlacedWT, spqrRecvKeyDeriveRawSpecPlacedWT,
        LibsignalBinary.Proofs.TripleRatchet.Decrypt.KeyDeriveBaseBudget.spqrRecvRawSpecPlaced,
        withLsCodeRoLoaded] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      refine sepConj_mono_right (Entails.sepExists_mono fun evs => ?_)
      simp only [vecArg_at_atState, spqrRecvResultAt_atState, RustCliAllocBudget.atState_pool]
      apply Entails.pure_left; rintro ⟨htr, hnp, hevs⟩
      exact Entails.pure_right hevs (Entails.pure_right ⟨htr, hnp⟩ (Entails.refl _)))
    (fun _ _ _ _ hpan => hpan)
    (fun _ _ _ _ _ he => he)

theorem spqrRecvPqSpecPlacedWT_ok_of_v1 {MC : AllocCostModel}
    {prog : Program} {entry_pc : BitVec 64}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (F : ShaCompress) (K : MlKem)
    (RcvPred : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (hRecvV1 : subroutine_ok prog entry_pc
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) (fun st msg => RcvPred st.bytes msg.bytes))) :
    subroutine_ok prog entry_pc
      (spqrRecvPqSpecPlacedWT A lim (spqrV1 F K) RcvPred) :=
  spqrRecvPqSpecPlacedWT_ok_of_keyDeriveWT A lim (spqrV1 F K) RcvPred
    (spqrRecvKeyDeriveSpecPlacedWT_ok_of_v1 A lim F K RcvPred hRecvV1)

theorem spqr_recv_keyDeriveWT_placed_ok_blockProgram_of_contracts_c07TightLinked
    {MC : AllocCostModel} {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvEnv' g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvKeyDeriveSpecPlacedWT A lim (spqrV1 F K)
        (fun stBytes _msgBytes evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqrRecvKeyDeriveSpecPlacedWT_ok_of_v1 A lim F K
    (fun stBytes _msgBytes evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    (spqr_recv_placed_ok_blockProgram_of_contracts_c07TightLinked hC)

/-- Linked `Block 329` (`spqr::recv`) witness at `spqrRecvPqSpecPlacedWT` (`spqrV1 F K`, `SpqrRecvC07TightLinkedEnv`).
-/
theorem spqr_recv_pqWT_placed_ok_blockProgram_of_contracts_c07TightLinked
    {MC : AllocCostModel} {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvEnv' g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPqSpecPlacedWT A lim (spqrV1 F K)
        (fun stBytes _msgBytes evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqrRecvPqSpecPlacedWT_ok_of_v1 A lim F K
    (fun stBytes _msgBytes evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
      SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
    (spqr_recv_placed_ok_blockProgram_of_contracts_c07TightLinked hC)

theorem spqr_recv_pqWT_placed_ok_blockProgram_of_contracts_c07c09aTightLinked
    {MC : AllocCostModel} {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC}
    {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      (fun _ => DecodeStateTightEnv) (fun _ => DecodeStateTightEnv)
      (InitInnerEnv F)
      (fun _ => StatesFromPbTightEnv)
      (fun g => StatesRecvProtoEnv g.self g.msg)
      (fun _ => StatesIntoPbTightEnv) ext) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPqSpecPlacedWT A lim (spqrV1 F K)
        (fun stBytes _msgBytes evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07C09aTightLinkedEnv F K
            stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)) :=
  spqr_recv_pqWT_placed_ok_blockProgram_of_contracts_c07TightLinked hC

end ProgramWitnesses

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWitness
