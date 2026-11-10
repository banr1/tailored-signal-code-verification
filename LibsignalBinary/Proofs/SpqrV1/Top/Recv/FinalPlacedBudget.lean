/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudgetAux

/-!
# Budget-Threaded Relocatable Top-Level Assembly for `spqr::recv`

Composes `SpqrRecvPlacedContractsOfEnv` and `SpqrRecvBranchHyps` to prove envelope-parametric and
default `SpqrRecvEnv` top-level `subroutine_ok` theorems for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPC_363 blkPC_364 blkPC_365 blkPC_366 blkPC_368 blkPl_363
   blkPl_364 blkPl_365 blkPl_366 blkPl_368 libsignalSessionLib lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State spqrHkdfWith spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg spqrRecvStack)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt spqrRecvPlacedEntry
   spqrRecvPlacedProg spqrRecvRoPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliDeallocBudgetSpec)
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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
  (StatesFromPbPlacedOkXOfEnv StatesPlacedSeams StatesPlacedSeamsOfEnv StatesRecvPlacedOkXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStatePlacedOkOfEnv DecodeStatePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv InitInnerPlacedOkX SpqrBoundedEvs StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsPlacedBudget
  (MessageDeserializePlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (InitInnerPlacedOkXOfEnv StatesIntoPbPlacedOkX StatesIntoPbPlacedOkXOfEnv
   spqrRecvPlacedContractsOfEnv_of_callees spqrRecvPlacedContractsOfEnv_of_okX
   spqrRecvPlacedContracts_of_okX spqrRecvPlacedSpecXT spqrRecvPlacedSpecXTOfEnv
   spqrRecv_placed_ok_of_tails_ofEnv spqrRecv_placed_sepWPpLS_of_tails_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv StatesRecvEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudgetAux
  (SpqrRecvBranchHyps fitsEnv_step_of_extend fitsEnv_step_of_prefix initInnerPlacedTailGen_ok_ofEnv
   v0ChainPlacedTailGen_ok_ofEnv v1RatchetPlacedTailGen_ok_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv spqrRecvBudgetPanicPost spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

export CryptoVerification.SpqrV1.Top.Recv
  (sepWPpLS_intro_chunkedStatesLocal2JumpTablePlacedAt)
export LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudgetAux
  (fitsEnv_step_of_extend fitsEnv_step_of_prefix SpqrRecvBranchHyps
   v0ChainPlacedTailGen_ok_ofEnv initInnerPlacedTailGen_ok_ofEnv v1RatchetPlacedTailGen_ok_ofEnv)

variable [LibsignalPlacement]

/-! ## Top-Level Relocatable `spqr::recv` (`Block 329`) Composition -/

/-- Envelope-parametric `SepWPpLS` execution of `spqr::recv` (`Block 329`) from
    `SpqrRecvPlacedContractsOfEnv`, `spqrRecvStack ≤ s0.sp.toNat`, and `SpqrRecvBranchHyps`. -/
theorem spqrRecv_placed_sepWPpLS_of_contracts_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {st_cost : MC.σ} {F : ShaCompress} {K : MlKem}
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
    (hsp_lo : spqrRecvStack ≤ s0.sp.toNat)
    (hB : SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
      Env st msg s0 st_cost)
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
  spqrRecv_placed_sepWPpLS_of_tails_ofEnv H_inner Env hC st msg ret s0 P R hst_len
    hB.env_nil
    hB.fit_dec
    (fun pre hpre evs_dec hdec_env evs_d hd => hB.env_dec_free pre evs_dec evs_d hpre hdec_env hd)
    (v0ChainPlacedTailGen_ok_ofEnv hC st msg ret s0 R hst_len hsp_align hB)
    (initInnerPlacedTailGen_ok_ofEnv hC st msg ret s0 R hst_len hsp_align hsp_lo hB)
    (v1RatchetPlacedTailGen_ok_ofEnv hC st msg ret s0 R hst_len hsp_align hsp_lo hB)
    hpc hrun hsp_align hx0 hx1 hx8 hP

/-- Envelope-parametric `subroutine_ok` proof that `spqr::recv` (`Block 329`) satisfies
    `spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env` on `spqrRecvPlacedProg ext` from
    `SpqrRecvPlacedContractsOfEnv` and `SpqrRecvBranchHyps`. -/
theorem spqrRecv_placed_ok_of_contracts_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
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
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
        (Env st msg) st msg s0 st_cost) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) :=
  spqrRecv_placed_ok_of_tails_ofEnv H_inner Env hC hnil
    (fun st msg _ret s0 st_cost pre hst hmsg halign hsp hfit hpre =>
      (hB st msg s0 st_cost hst hmsg halign hsp hfit).fit_dec pre hpre)
    (fun st msg _ret s0 st_cost pre hst hmsg halign hsp hfit hpre evs_dec hdec_env evs_d hd =>
      (hB st msg s0 st_cost hst hmsg halign hsp hfit).env_dec_free pre evs_dec evs_d hpre hdec_env hd)
    (fun st msg ret s0 st_cost R hst hmsg halign hsp hfit =>
      v0ChainPlacedTailGen_ok_ofEnv hC st msg ret s0 R hst halign
        (hB st msg s0 st_cost hst hmsg halign hsp hfit))
    (fun st msg ret s0 st_cost R hst hmsg halign hsp hfit =>
      initInnerPlacedTailGen_ok_ofEnv hC st msg ret s0 R hst halign hsp
        (hB st msg s0 st_cost hst hmsg halign hsp hfit))
    (fun st msg ret s0 st_cost R hst hmsg halign hsp hfit =>
      v1RatchetPlacedTailGen_ok_ofEnv hC st msg ret s0 R hst halign hsp
        (hB st msg s0 st_cost hst hmsg halign hsp hfit))

theorem spqr_recv_placed_ok_of_contracts_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
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
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
        (Env st msg) st msg s0 st_cost) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) :=
  spqrRecv_placed_ok_of_contracts_ofEnv Env hC hnil hB

theorem spqr_recv_placed_ok_blockProgram_of_contracts_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
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
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
        (Env st msg) st msg s0 st_cost) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) := by
  have hok := spqr_recv_placed_ok_of_contracts_ofEnv Env hC hnil hB
  rwa [← IsLsBlockProg.eq_blockProgram (prog := spqrRecvPlacedProg ext)]

theorem spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (Env : VecArg → VecArg → List AllocEvent → Prop)
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (hnil : ∀ (st msg : VecArg), st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      (∃ st_cost : MC.σ, FitsEnv MC lim st_cost (Env st msg)) → Env st msg [])
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
        (Env st msg) st msg s0 st_cost) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 ext)
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) := by
  have heq : Rust.withPanics ext = ext := by
    funext sym; unfold Rust.withPanics; split
    · next h => exact (hp sym h).symm
    · rfl
  simpa only [heq] using spqr_recv_placed_ok_blockProgram_of_contracts_ofEnv Env hC hnil hB

/-- Envelope-parametric relocatable `spqr::recv` (`Block 329`) theorem taking
    `StatesFromPbPlacedOkXOfEnv` and `StatesRecvPlacedOkXOfEnv` directly (without send-chunk
    seams). -/
theorem spqr_recv_placed_ok_of_callees_ofEnv {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (Env : VecArg → VecArg → List AllocEvent → Prop)
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
    (hEncodeToVec : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hnil : ∀ (st msg : VecArg), st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      (∃ st_cost : MC.σ, FitsEnv MC lim st_cost (Env st msg)) → Env st msg [])
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
        (Env st msg) st msg s0 st_cost) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) :=
  spqr_recv_placed_ok_of_contracts_ofEnv Env
    (spqrRecvPlacedContractsOfEnv_of_callees hdealloc hmemcpy
      hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
      hDropPqRatchetState hDropStates
      hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hMsgDeser hStatesFromPb hStatesRecv hStatesIntoPb hEncodeToVec)
    hnil hB

/-- Top-level envelope-parametric relocatable `spqr::recv` (`Block 329`) theorem parameterized
    by `StatesPlacedSeamsOfEnv` and placed callee contracts. -/
theorem spqr_recv_placed_ok_ofEnv {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
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
    (Env : VecArg → VecArg → List AllocEvent → Prop)
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
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    (hnil : ∀ (st msg : VecArg), st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      (∃ st_cost : MC.σ, FitsEnv MC lim st_cost (Env st msg)) → Env st msg [])
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
        (Env st msg) st msg s0 st_cost) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) :=
  spqr_recv_placed_ok_of_contracts_ofEnv Env
    (spqrRecvPlacedContractsOfEnv_of_okX hdealloc hmemcpy
      hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
      hDropPqRatchetState hDropStates
      hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hMsgDeser hStatesIntoPb hEncodeToVec hSeams)
    hnil hB

theorem spqr_recv_placed_ok_blockProgram_ofEnv {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
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
    (Env : VecArg → VecArg → List AllocEvent → Prop)
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
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    (hnil : ∀ (st msg : VecArg), st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      (∃ st_cost : MC.σ, FitsEnv MC lim st_cost (Env st msg)) → Env st msg [])
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (Env st msg) →
      SpqrRecvBranchHyps lim F K DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv
        (Env st msg) st msg s0 st_cost) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXTOfEnv A lim (spqrV1Recv F K) Env) :=
  spqr_recv_placed_ok_blockProgram_of_contracts_ofEnv Env
    (spqrRecvPlacedContractsOfEnv_of_okX hdealloc hmemcpy
      hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
      hDropPqRatchetState hDropStates
      hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hMsgDeser hStatesIntoPb hEncodeToVec hSeams)
    hnil hB

theorem spqr_recv_placed_ok_of_contracts {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      SpqrRecvBranchHyps lim F K DecodeStateEnv DecodeStateEnv (InitInnerEnv F)
        StatesFromPbEnv StatesRecvEnv StatesIntoPbEnv (SpqrRecvEnv st msg) st msg s0 st_cost) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXT A lim (spqrV1Recv F K)) :=
  spqr_recv_placed_ok_of_contracts_ofEnv SpqrRecvEnv hC
    (fun _ _ _ _ _ => SpqrBoundedEvs.nil _ _)
    hB

theorem spqr_recv_placed_ok_blockProgram_ext_of_contracts {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hp : ∀ sym, Rust.isPanicSymbol sym = true → ext sym = some Rust.panicked)
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      SpqrRecvBranchHyps lim F K DecodeStateEnv DecodeStateEnv (InitInnerEnv F)
        StatesFromPbEnv StatesRecvEnv StatesIntoPbEnv (SpqrRecvEnv st msg) st msg s0 st_cost) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 ext)
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXT A lim (spqrV1Recv F K)) :=
  spqr_recv_placed_ok_blockProgram_ext_of_contracts_ofEnv SpqrRecvEnv hp hC
    (fun _ _ _ _ _ => SpqrBoundedEvs.nil _ _)
    hB

theorem spqr_recv_placed_ok {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
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
    (hSeams : StatesPlacedSeams MC A lim F K ext)
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      SpqrRecvBranchHyps lim F K DecodeStateEnv DecodeStateEnv (InitInnerEnv F)
        StatesFromPbEnv StatesRecvEnv StatesIntoPbEnv (SpqrRecvEnv st msg) st msg s0 st_cost) :
    subroutine_ok (spqrRecvPlacedProg ext) spqrRecvPlacedEntry
      (spqrRecvPlacedSpecXT A lim (spqrV1Recv F K)) :=
  spqr_recv_placed_ok_of_contracts
    (spqrRecvPlacedContracts_of_okX hdealloc hmemcpy
      hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
      hDropPqRatchetState hDropStates
      hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch hChainRecvKey hChainIntoPb
      hMsgDeser hStatesIntoPb hEncodeToVec hSeams)
    hB

theorem spqr_recv_placed_ok_blockProgram {MC : AllocCostModel}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits}
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
    (hSeams : StatesPlacedSeams MC A lim F K ext)
    (hB : ∀ (st msg : VecArg) (s0 : State) (st_cost : MC.σ),
      st.bytes.length < 2 ^ 32 → msg.bytes.length < 2 ^ 40 →
      s0.spAligned = true → spqrRecvStack ≤ s0.sp.toNat →
      FitsEnv MC lim st_cost (SpqrRecvEnv st msg) →
      SpqrRecvBranchHyps lim F K DecodeStateEnv DecodeStateEnv (InitInnerEnv F)
        StatesFromPbEnv StatesRecvEnv StatesIntoPbEnv (SpqrRecvEnv st msg) st msg s0 st_cost) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 329 (Rust.withPanics ext))
      (lsmpl.base 329)
      (spqrRecvPlacedSpecXT A lim (spqrV1Recv F K)) :=
  spqr_recv_placed_ok_blockProgram_ofEnv SpqrRecvEnv
    hdealloc hmemcpy hDropEpochSlice hDropOptProtoInnerState hDropOptProtoChain hDropChain
    hDropPqRatchetState hDropStates hDecodeState hInitInner hChainFromPb hChainNew hChainAddEpoch
    hChainRecvKey hChainIntoPb hMsgDeser hStatesIntoPb hEncodeToVec hSeams
    (fun _ _ _ _ _ => SpqrBoundedEvs.nil _ _)
    hB

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlacedBudget
