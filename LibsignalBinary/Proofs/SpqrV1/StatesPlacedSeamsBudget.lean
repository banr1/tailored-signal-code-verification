/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeams
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget

/-!
# Budget-Threaded `[LibsignalPlacement]` Seams for `SpqrV1/States`

`RustCliAllocBudget` specifications, allocation-event envelopes, cross-block transfer helpers,
and `StatesPlacedSeams` bundle for `SpqrV1/States/{FromPb,Recv,Leaves}`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (IsLsBlockProg LibsignalPlacement libsignalSessionLib lsmpl)
open CryptoVerification.LibsignalSpqrV1 (MlKem V1State)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.SpqrV1
  (ls_subroutine_ok_of_blockProgram_cro ls_subroutine_ok_to_blockProgram)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (Ct1ReceivedSendEkChunkEnv Ct1ReceivedSendEkChunkPlacedOkX
   Ct1ReceivedSendEkChunkPlacedOkXOfEnv Ct1SampledSendCt1ChunkEnv
   Ct1SampledSendCt1ChunkPlacedOkX Ct1SampledSendCt1ChunkPlacedOkXOfEnv
   Ct2SampledSendCt2ChunkEnv Ct2SampledSendCt2ChunkPlacedOkX
   Ct2SampledSendCt2ChunkPlacedOkXOfEnv EkReceivedCt1SampledSendCt1ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkPlacedOkX EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv
   HeaderSentSendEkChunkEnv HeaderSentSendEkChunkPlacedOkX HeaderSentSendEkChunkPlacedOkXOfEnv
   ct1ReceivedSendEkChunkEnv_nonempty ct1ReceivedSendEkChunkPlacedSpec
   ct1ReceivedSendEkChunkPlacedSpecOfEnv ct1SampledSendCt1ChunkEnv_nonempty
   ct1SampledSendCt1ChunkPlacedSpec ct1SampledSendCt1ChunkPlacedSpecOfEnv
   ct2SampledSendCt2ChunkEnv_nonempty ct2SampledSendCt2ChunkPlacedSpec
   ct2SampledSendCt2ChunkPlacedSpecOfEnv ekReceivedCt1SampledSendCt1ChunkEnv_nonempty
   ekReceivedCt1SampledSendCt1ChunkPlacedSpec ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv
   headerSentSendEkChunkEnv_nonempty headerSentSendEkChunkPlacedSpec
   headerSentSendEkChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (StatesRecvEnv statesFromPbPlacedSpecX statesFromPbPlacedSpecXOfEnv
   statesRecvPlacedSpec statesRecvPlacedSpecOfEnv)

/-! ## Cross-Block `withLsCodeRoLoaded` Transfer from `blockProgram` -/

export CryptoVerification.SpqrV1
  (ls_subroutine_ok_of_blockProgram_cro ls_subroutine_ok_to_blockProgram)

/-! ## Relocatable `[LibsignalPlacement]` Budget Specifications for `States/Leaves` Send Chunks -/

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (EkReceivedCt1SampledSendCt1ChunkEnv ekReceivedCt1SampledSendCt1ChunkEnv_nonempty
   ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv ekReceivedCt1SampledSendCt1ChunkPlacedSpec
   Ct2SampledSendCt2ChunkEnv ct2SampledSendCt2ChunkEnv_nonempty
   ct2SampledSendCt2ChunkPlacedSpecOfEnv ct2SampledSendCt2ChunkPlacedSpec
   HeaderSentSendEkChunkEnv headerSentSendEkChunkEnv_nonempty
   headerSentSendEkChunkPlacedSpecOfEnv headerSentSendEkChunkPlacedSpec
   Ct1ReceivedSendEkChunkEnv ct1ReceivedSendEkChunkEnv_nonempty
   ct1ReceivedSendEkChunkPlacedSpecOfEnv ct1ReceivedSendEkChunkPlacedSpec
   Ct1SampledSendCt1ChunkEnv ct1SampledSendCt1ChunkEnv_nonempty
   ct1SampledSendCt1ChunkPlacedSpecOfEnv ct1SampledSendCt1ChunkPlacedSpec)

/-! ## Per-Block Budget Contract Predicates (`*PlacedOkXOfEnv` & `*PlacedOkX`) -/

/-- Envelope-parametric Block `333` contract: `<States>::from_pb` meets
    `withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env)`. -/
def StatesFromPbPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    (Env : V1State → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
    (lsmpl.base 333) (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F Env))

/-- Default Block `333` contract: `<States>::from_pb` meets
    `withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)`. -/
abbrev StatesFromPbPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  StatesFromPbPlacedOkXOfEnv M A lim F ext StatesFromPbEnv

/-- Envelope-parametric Block `332` contract: `<States>::recv` meets
    `withLsCodeRoLoaded lsmpl (statesRecvPlacedSpecOfEnv M A lim F K Env)`. -/
def StatesRecvPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (Env : StatesRecvGhost F → List AllocEvent → Prop) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext))
    (lsmpl.base 332) (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpecOfEnv M A lim F K Env))

/-- Default Block `332` contract: `<States>::recv` meets
    `withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec M A lim F K)`. -/
abbrev StatesRecvPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  StatesRecvPlacedOkXOfEnv M A lim F K ext StatesRecvEnv

export LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
  (HeaderSentSendEkChunkPlacedOkXOfEnv HeaderSentSendEkChunkPlacedOkX
   Ct1ReceivedSendEkChunkPlacedOkXOfEnv Ct1ReceivedSendEkChunkPlacedOkX
   Ct1SampledSendCt1ChunkPlacedOkXOfEnv Ct1SampledSendCt1ChunkPlacedOkX
   EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv EkReceivedCt1SampledSendCt1ChunkPlacedOkX
   Ct2SampledSendCt2ChunkPlacedOkXOfEnv Ct2SampledSendCt2ChunkPlacedOkX)

/-! ## Public Budget Seam Bundle (`StatesPlacedSeams`) & Caller-Block Transfer Helpers -/

/-- Envelope-parametric `[LibsignalPlacement]` budget seam bundle for
    `SpqrV1/States/{FromPb,Recv,Leaves}` (Blocks `332`, `333`, `335`, `336`, `344`, `345`, `354`). -/
structure StatesPlacedSeamsOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (FromPbEnv : V1State → List AllocEvent → Prop)
    (RecvEnv : StatesRecvGhost F → List AllocEvent → Prop)
    (HsEkEnv : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop)
    (Ct1rEkEnv : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop)
    (Ct1sEnv : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (EkCt1sEnv : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (Ct2sEnv : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  statesFromPb_ok : StatesFromPbPlacedOkXOfEnv M A lim F ext FromPbEnv
  statesRecv_ok : StatesRecvPlacedOkXOfEnv M A lim F K ext RecvEnv
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F ext HsEkEnv
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F ext Ct1rEkEnv
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F ext Ct1sEnv
  ekReceivedCt1SampledSendCt1Chunk_ok :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F ext EkCt1sEnv
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F ext Ct2sEnv

/-- Default `[LibsignalPlacement]` budget seam bundle for `SpqrV1/States/{FromPb,Recv,Leaves}`. -/
abbrev StatesPlacedSeams [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  StatesPlacedSeamsOfEnv M A lim F K
    StatesFromPbEnv StatesRecvEnv
    HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
    Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
    ext

namespace StatesPlacedSeamsOfEnv

variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {F : ShaCompress} {K : MlKem}
  {FromPbEnv : V1State → List AllocEvent → Prop}
  {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
  {HsEkEnv : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
  {Ct1rEkEnv : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
  {Ct1sEnv : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
  {EkCt1sEnv : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
  {Ct2sEnv : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
  {ext : String → Option (State → State)}

theorem statesFromPb_on
    (h : StatesPlacedSeamsOfEnv M A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim F FromPbEnv)) :=
  ls_subroutine_ok_of_blockProgram_cro h.statesFromPb_ok hi

theorem statesRecv_on
    (h : StatesPlacedSeamsOfEnv M A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpecOfEnv M A lim F K RecvEnv)) :=
  ls_subroutine_ok_of_blockProgram_cro h.statesRecv_ok hi

theorem headerSentSendEkChunk_on
    (h : StatesPlacedSeamsOfEnv M A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 336)
      (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpecOfEnv M A lim F HsEkEnv)) :=
  ls_subroutine_ok_of_blockProgram_cro h.headerSentSendEkChunk_ok hi

theorem ct1ReceivedSendEkChunk_on
    (h : StatesPlacedSeamsOfEnv M A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 345)
      (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Ct1rEkEnv)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ct1ReceivedSendEkChunk_ok hi

theorem ct1SampledSendCt1Chunk_on
    (h : StatesPlacedSeamsOfEnv M A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 335)
      (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Ct1sEnv)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ct1SampledSendCt1Chunk_ok hi

theorem ekReceivedCt1SampledSendCt1Chunk_on
    (h : StatesPlacedSeamsOfEnv M A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 344)
      (withLsCodeRoLoaded lsmpl
        (ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F EkCt1sEnv)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ekReceivedCt1SampledSendCt1Chunk_ok hi

theorem ct2SampledSendCt2Chunk_on
    (h : StatesPlacedSeamsOfEnv M A lim F K
      FromPbEnv RecvEnv HsEkEnv Ct1rEkEnv Ct1sEnv EkCt1sEnv Ct2sEnv ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 354)
      (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F Ct2sEnv)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ct2SampledSendCt2Chunk_ok hi

end StatesPlacedSeamsOfEnv

namespace StatesPlacedSeams

variable [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}

theorem statesFromPb_on (h : StatesPlacedSeams M A lim F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX M A lim F)) :=
  StatesPlacedSeamsOfEnv.statesFromPb_on h hi

theorem statesRecv_on (h : StatesPlacedSeams M A lim F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec M A lim F K)) :=
  StatesPlacedSeamsOfEnv.statesRecv_on h hi

theorem headerSentSendEkChunk_on (h : StatesPlacedSeams M A lim F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 336)
      (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec M A lim F)) :=
  StatesPlacedSeamsOfEnv.headerSentSendEkChunk_on h hi

theorem ct1ReceivedSendEkChunk_on (h : StatesPlacedSeams M A lim F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 345)
      (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec M A lim F)) :=
  StatesPlacedSeamsOfEnv.ct1ReceivedSendEkChunk_on h hi

theorem ct1SampledSendCt1Chunk_on (h : StatesPlacedSeams M A lim F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 335)
      (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec M A lim F)) :=
  StatesPlacedSeamsOfEnv.ct1SampledSendCt1Chunk_on h hi

theorem ekReceivedCt1SampledSendCt1Chunk_on (h : StatesPlacedSeams M A lim F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 344)
      (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec M A lim F)) :=
  StatesPlacedSeamsOfEnv.ekReceivedCt1SampledSendCt1Chunk_on h hi

theorem ct2SampledSendCt2Chunk_on (h : StatesPlacedSeams M A lim F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 354)
      (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec M A lim F)) :=
  StatesPlacedSeamsOfEnv.ct2SampledSendCt2Chunk_on h hi

end StatesPlacedSeams

end LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
