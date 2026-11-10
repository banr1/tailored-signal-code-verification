/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.ProofPlaced -- shake: keep

/-!
# Budget-Threaded Relocatable Definitions and Callee Contracts for `spqr::send::<HookRng>` (Block 124)

Defines envelope-parametric and default `RustCliAllocBudget` callee contract bundles
(`SpqrSendPlacedContractsOfEnv`, `SpqrSendPlacedContracts`) for Block 124 under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem PolyApi V1State spqrHkdfWith spqrPolyApi)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (EncodeBytesGhost)
open CryptoVerification.SpqrV1.Poly.NextChunk (PolyNextChunkGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost messageAt messageSerializeStackX)
open CryptoVerification.SpqrV1.Top.Send
  (spqrSendDropJumpTablePlacedAt spqrSendEncodeJumpTablePlacedAt spqrSendPlacedEntry
   spqrSendPlacedProg spqrSendRoPlacedAt spqrSendRoSym spqrSendStatesJumpTablePlacedAt
   spqrSendStatesJumpTablePlacedAt_eq_words)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget (authMacHdrSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget (authUpdateSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (hkdfToVecSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesSpecX encodeBytesSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (PolyNextChunkEnv polyNextChunkPlacedSpec polyNextChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv
   ct1ReceivedSendEkChunkPlacedSpec ct1ReceivedSendEkChunkPlacedSpecOfEnv
   ct1SampledSendCt1ChunkPlacedSpec ct1SampledSendCt1ChunkPlacedSpecOfEnv
   ct2SampledSendCt2ChunkPlacedSpec ct2SampledSendCt2ChunkPlacedSpecOfEnv
   ekReceivedCt1SampledSendCt1ChunkPlacedSpec ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv
   headerSentSendEkChunkPlacedSpec headerSentSendEkChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
  (MessageSerializeEnv messageSerializeEvents messageSerializeSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (decodeStatePlacedSpecX decodeStatePlacedSpecXOfEnv statesFromPbPlacedSpecX
   statesFromPbPlacedSpecXOfEnv statesIntoPbPlacedSpecX statesIntoPbPlacedSpecXOfEnv)

variable [LibsignalPlacement]

/-! ## Re-Exports of Block 124 Program, `.rodata` Bundles, and `AllocContractsPlaced` -/

export CryptoVerification.SpqrV1.Top.Send
  (spqrSendPlacedProg spqrSendPlacedEntry spqrSendRoSym spqrSendRoPlacedAt)

export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced)

export LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
  (MessageSerializeEnv messageSerializeEvents messageSerializeSpecX)

/-! ## `<Message>::serialize` and Leaf `PlacedOkX` Budget Contracts -/

/-- Envelope-parametric budget-threaded specification of `<spqr::v1::chunked::states::Message>::serialize`
    (Block `352`, `110` insns) at `messageSerializeStackX`. -/
def messageSerializeSpecXOfEnv (P_api : PolyApi) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : MessageSerializeGhost P_api → List AllocEvent → Prop) :
    Spec (MessageSerializeGhost P_api × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ (s.readReg64 .x1).setWidth 32 = x.index ∧
      s.readReg64 .x8 = x.ret ∧ FitsEnv M lim st (Env x)⌝ ∗
      messageAt P_api x.msgA x.msg ∗ memRegion x.ret 24 ∗ A.pool lim st s ∗
      stackAt s.sp messageSerializeStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      messageAt P_api x.msgA x.msg ∗
      vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
      (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp messageSerializeStackX

omit [LibsignalPlacement] in
theorem messageSerializeSpecXOfEnv_eq (P_api : PolyApi) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    messageSerializeSpecXOfEnv P_api A lim (MessageSerializeEnv P_api) =
      messageSerializeSpecX P_api A lim := rfl

/-- Envelope-parametric Block `416` contract on `spqrSendPlacedProg ext`:
    `<PolyEncoder as Encoder>::next_chunk` meets
    `withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim)`. -/
def PolyNextChunkPlacedOkXOfEnv
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 416)
    (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim))

abbrev PolyNextChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkPlacedOkXOfEnv PolyNextChunkEnv M A lim ext

/-- Envelope-parametric Block `417` contract on `spqrSendPlacedProg ext`:
    `<PolyEncoder>::encode_bytes` meets
    `withLsCodeRoLoaded lsmpl (encodeBytesSpecXOfEnv A lim PreEnv PostEnv)`. -/
def EncodeBytesPlacedOkXOfEnv {M : AllocCostModel}
    (PreEnv PostEnv : EncodeBytesGhost → List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 417)
    (withLsCodeRoLoaded lsmpl (encodeBytesSpecXOfEnv A lim PreEnv PostEnv))

abbrev EncodeBytesPlacedOkX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeBytesPlacedOkXOfEnv
    (fun x => EncodeBytesEnv x.msg.length)
    (fun x => EncodeBytesEnv x.msg.length)
    A lim ext

def HeaderSentSendEkChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 336)
    (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpecOfEnv M A lim F Env))

abbrev HeaderSentSendEkChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F HeaderSentSendEkChunkEnv ext

def Ct1ReceivedSendEkChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 345)
    (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Env))

abbrev Ct1ReceivedSendEkChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F Ct1ReceivedSendEkChunkEnv ext

def Ct1SampledSendCt1ChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 335)
    (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env))

abbrev Ct1SampledSendCt1ChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F Ct1SampledSendCt1ChunkEnv ext

def EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 344)
    (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env))

abbrev EkReceivedCt1SampledSendCt1ChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F EkReceivedCt1SampledSendCt1ChunkEnv ext

def Ct2SampledSendCt2ChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 354)
    (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F Env))

abbrev Ct2SampledSendCt2ChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F Ct2SampledSendCt2ChunkEnv ext

/-! ## Relocatable Budget Callee Contract Bundle (`SpqrSendPlacedContractsOfEnv`) -/

/-- Envelope-parametric relocatable `[LibsignalPlacement]` bundle of budget-threaded callee
    contracts required by `spqr::send::<libsignal_session::HookRng>` (Block `124`). -/
structure SpqrSendPlacedContractsOfEnv {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (FromPbEnv : V1State → List AllocEvent → Prop)
    (IntoPbEnv : StatesIntoPbGhost C.F → List AllocEvent → Prop)
    (MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop)
    (EncPreEnv EncPostEnv : EncodeBytesGhost → List AllocEvent → Prop)
    (NextChunkEnv : PolyNextChunkGhost → List AllocEvent → Prop)
    (HsEkEnv : HeaderSentSendEkChunkGhost C.F → List AllocEvent → Prop)
    (Ct1rEkEnv : Ct1ReceivedSendEkChunkGhost C.F → List AllocEvent → Prop)
    (Ct1sEnv : Ct1SampledSendCt1ChunkGhost C.F → List AllocEvent → Prop)
    (EkCt1sEnv : EkReceivedCt1SampledSendCt1ChunkGhost C.F → List AllocEvent → Prop)
    (Ct2sEnv : Ct2SampledSendCt2ChunkGhost C.F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  /-- Representation equivalence between `DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st`
      and `Drop.optProtoInnerStateAt A.repAlloc a st`. -/
  h_inner_eq :
    ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a st
  /-- Rust heap allocator + `memcpy` + `memcmp` budget contracts under `[LibsignalPlacement]`. -/
  alloc : AllocContractsPlaced M A lim ext
  /-- `spqr::decode_state` (Block `325`). -/
  decodeState_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecXOfEnv H_inner A lim DecodePreEnv DecodePostEnv))
  /-- `<States>::from_pb` (Block `333`). -/
  statesFromPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim C.F FromPbEnv))
  /-- `<States>::into_pb` (Block `334`). -/
  statesIntoPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim C.F IntoPbEnv))
  /-- `<Chain>::from_pb` (Block `364`). -/
  chainFromPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim))
  /-- `spqr::chain_from_version_negotiation` (Block `328`). -/
  chainFromVn_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith C.F) M A lim))
  /-- `<Chain>::add_epoch` (Block `368`). -/
  chainAddEpoch_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith C.F) M A lim))
  /-- `<Chain>::send_key` (Block `367`). -/
  chainSendKey_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith C.F) M A lim))
  /-- `<Chain>::into_pb` (Block `365`). -/
  chainIntoPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim))
  /-- `<Message>::serialize` (Block `352`). -/
  messageSerialize_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi A lim MsgSerEnv))
  /-- `spqr::encode_varint` (Block `326`). -/
  encodeVarint_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim))
  /-- `<Authenticator>::mac_hdr` (Block `342`). -/
  authMacHdr_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrSpec C.F M A lim))
  /-- `<Authenticator>::update` (Block `341`). -/
  authUpdate_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec C.F M A lim))
  /-- `spqr::kdf::hkdf_to_vec` (Block `378`). -/
  hkdfToVec_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F)))
  /-- `<PolyEncoder>::encode_bytes` (Block `417`). -/
  encodeBytes_ok : EncodeBytesPlacedOkXOfEnv EncPreEnv EncPostEnv A lim ext
  /-- `<PolyEncoder as Encoder>::next_chunk` (Block `416`). -/
  polyNextChunk_ok : PolyNextChunkPlacedOkXOfEnv NextChunkEnv M A lim ext
  /-- Leaf `<HeaderSent>::send_ek_chunk` (Block `336`). -/
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkPlacedOkXOfEnv M A lim C.F HsEkEnv ext
  /-- Leaf `<Ct1Received>::send_ek_chunk` (Block `345`). -/
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim C.F Ct1rEkEnv ext
  /-- Leaf `<Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim C.F Ct1sEnv ext
  /-- Leaf `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
  ekReceivedCt1SampledSendCt1Chunk_ok :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim C.F EkCt1sEnv ext
  /-- Leaf `<Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim C.F Ct2sEnv ext
  /-- `drop_glue::<proto::Chain> [local#1]` (Block `136`). -/
  dropProtoChain_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim))
  /-- `drop_glue::<[chain::Epoch]> [local#1]` (Block `143`). -/
  dropChainEpochSlice_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 143)
      (withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec M A lim))

/-- Default relocatable `[LibsignalPlacement]` bundle of budget-threaded callee contracts required
    by `spqr::send::<libsignal_session::HookRng>` (Block `124`). -/
abbrev SpqrSendPlacedContracts {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  SpqrSendPlacedContractsOfEnv H_inner A lim ctl C K
    DecodeStateEnv DecodeStateEnv
    StatesFromPbEnv StatesIntoPbEnv
    (MessageSerializeEnv spqrPolyApi)
    (fun x => EncodeBytesEnv x.msg.length)
    (fun x => EncodeBytesEnv x.msg.length)
    PolyNextChunkEnv
    HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
    Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
    ext

end LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlacedBudget
