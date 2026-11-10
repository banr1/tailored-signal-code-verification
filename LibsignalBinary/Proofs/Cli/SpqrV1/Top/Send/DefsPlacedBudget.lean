/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
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
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget

/-!
# Budget-Threaded Relocatable Definitions & Callee Contracts for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Defines budget-threaded callee contract bundles and allocator/VM-preservation predicates
for Block `427` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (MlKem PolyApi V1State spqrHkdfWith spqrPolyApi)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (EncodeBytesGhost)
open CryptoVerification.SpqrV1.Poly.NextChunk (PolyNextChunkGhost)
open CryptoVerification.SpqrV1.States.FromPb (StatesFromPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost V1InnerHeapPred)
open CryptoVerification.SpqrV1.Top.MessageSerialize (MessageSerializeGhost)
open CryptoVerification.SpqrV1.Top.Send (spqrSendCalleeStack)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedProg)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (DecodeStatePlacedEnv MessageSerializeEnv SpqrSendChunkEnv StatesFromPbEnv
   ct1ReceivedSendEkChunkPlacedSpec ct1ReceivedSendEkChunkPlacedSpecOfEnv
   ct1SampledSendCt1ChunkPlacedSpec ct1SampledSendCt1ChunkPlacedSpecOfEnv
   ct2SampledSendCt2ChunkPlacedSpec ct2SampledSendCt2ChunkPlacedSpecOfEnv
   decodeStatePlacedSpecX decodeStatePlacedSpecXOfEnv
   ekReceivedCt1SampledSendCt1ChunkPlacedSpec ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv
   headerSentSendEkChunkPlacedSpec headerSentSendEkChunkPlacedSpecOfEnv
   messageSerializeSpecX messageSerializeSpecXOfEnv
   spqrCoinsFillSpecPlaced statesFromPbPlacedSpecX statesFromPbPlacedSpecXOfEnv)
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
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (spqrDecodeStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (StatesIntoPbEnv statesIntoPbPlacedSpecX statesIntoPbPlacedSpecXOfEnv)

variable [LibsignalPlacement]

/-! ## 1. Re-Exports of Allocator-Free Block `427` Definitions, `.rodata` & `AllocContractsPlaced` -/

export CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendPlacedProg cliSpqrSendPlacedProg spqrSendPlacedEntry cliSpqrSendPlacedEntry
   spqrSendRoSym)

export CryptoVerification.Cli.SpqrV1.Top.Send
  (cliSpqrSendRoSym cliSpqrSendLanon29Sym cliSpqrSendCst32Sym spqrLogLevelZeroPlacedAt
   spqrSendStatesJumpTablePlacedAt)

export CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendEncodeJumpTablePlacedAt spqrSendDropJumpTablePlacedAt spqrSendRoPlacedAt
   spqrSendStatesJumpTablePlacedAt_eq_words)

export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced)

/-! ## 2. Budget-Threaded Leaf `PlacedOkX` Contracts on `spqrSendPlacedProg` (Block `427`) -/

/-- Envelope-parametric `<PolyEncoder as Encoder>::next_chunk` (Block `416`) on `spqrSendPlacedProg ext`. -/
def PolyNextChunkPlacedOkXOfEnv
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 416)
    (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpecOfEnv Env M A lim))

/-- Canonical `<PolyEncoder as Encoder>::next_chunk` (Block `416`) on `spqrSendPlacedProg ext`. -/
abbrev PolyNextChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkPlacedOkXOfEnv PolyNextChunkEnv M A lim ext

/-- Envelope-parametric `<PolyEncoder as Encoder>::encode_bytes` (Block `417`) on `spqrSendPlacedProg ext`. -/
def EncodeBytesPlacedOkXOfEnv {M : AllocCostModel}
    (PreEnv PostEnv : EncodeBytesGhost → List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 417)
    (withLsCodeRoLoaded lsmpl (encodeBytesSpecXOfEnv A lim PreEnv PostEnv))

/-- Canonical `<PolyEncoder as Encoder>::encode_bytes` (Block `417`) on `spqrSendPlacedProg ext`. -/
abbrev EncodeBytesPlacedOkX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  EncodeBytesPlacedOkXOfEnv
    (fun x => EncodeBytesEnv x.msg.length) (fun x => EncodeBytesEnv x.msg.length) A lim ext

/-- Envelope-parametric `<HeaderSent>::send_ek_chunk` (Block `336`) on `spqrSendPlacedProg ext`. -/
def HeaderSentSendEkChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 336)
    (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpecOfEnv M A lim F Env))

/-- Peer-seam default (`SpqrSendChunkEnv`) `<HeaderSent>::send_ek_chunk` (Block `336`) on `spqrSendPlacedProg ext`. -/
abbrev HeaderSentSendEkChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F (fun _ => SpqrSendChunkEnv) ext

/-- Tight exact-envelope (`HeaderSentSendEkChunkEnv`) `<HeaderSent>::send_ek_chunk` (Block `336`) on `spqrSendPlacedProg ext`. -/
abbrev HeaderSentSendEkChunkTightPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  HeaderSentSendEkChunkPlacedOkXOfEnv M A lim F HeaderSentSendEkChunkEnv ext

/-- Envelope-parametric `<Ct1Received>::send_ek_chunk` (Block `345`) on `spqrSendPlacedProg ext`. -/
def Ct1ReceivedSendEkChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 345)
    (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpecOfEnv M A lim F Env))

/-- Peer-seam default (`SpqrSendChunkEnv`) `<Ct1Received>::send_ek_chunk` (Block `345`) on `spqrSendPlacedProg ext`. -/
abbrev Ct1ReceivedSendEkChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F (fun _ => SpqrSendChunkEnv) ext

/-- Tight exact-envelope (`Ct1ReceivedSendEkChunkEnv`) `<Ct1Received>::send_ek_chunk` (Block `345`) on `spqrSendPlacedProg ext`. -/
abbrev Ct1ReceivedSendEkChunkTightPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim F Ct1ReceivedSendEkChunkEnv ext

/-- Envelope-parametric `<Ct1Sampled>::send_ct1_chunk` (Block `335`) on `spqrSendPlacedProg ext`. -/
def Ct1SampledSendCt1ChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 335)
    (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env))

/-- Peer-seam default (`SpqrSendChunkEnv`) `<Ct1Sampled>::send_ct1_chunk` (Block `335`) on `spqrSendPlacedProg ext`. -/
abbrev Ct1SampledSendCt1ChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F (fun _ => SpqrSendChunkEnv) ext

/-- Tight exact-envelope (`Ct1SampledSendCt1ChunkEnv`) `<Ct1Sampled>::send_ct1_chunk` (Block `335`) on `spqrSendPlacedProg ext`. -/
abbrev Ct1SampledSendCt1ChunkTightPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F Ct1SampledSendCt1ChunkEnv ext

/-- Envelope-parametric `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`) on `spqrSendPlacedProg ext`. -/
def EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 344)
    (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpecOfEnv M A lim F Env))

/-- Peer-seam default (`SpqrSendChunkEnv`) `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`) on `spqrSendPlacedProg ext`. -/
abbrev EkReceivedCt1SampledSendCt1ChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F (fun _ => SpqrSendChunkEnv) ext

/-- Tight exact-envelope (`EkReceivedCt1SampledSendCt1ChunkEnv`) `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`) on `spqrSendPlacedProg ext`. -/
abbrev EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim F EkReceivedCt1SampledSendCt1ChunkEnv ext

/-- Envelope-parametric `<Ct2Sampled>::send_ct2_chunk` (Block `354`) on `spqrSendPlacedProg ext`. -/
def Ct2SampledSendCt2ChunkPlacedOkXOfEnv
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 354)
    (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpecOfEnv M A lim F Env))

/-- Peer-seam default (`SpqrSendChunkEnv`) `<Ct2Sampled>::send_ct2_chunk` (Block `354`) on `spqrSendPlacedProg ext`. -/
abbrev Ct2SampledSendCt2ChunkPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F (fun _ => SpqrSendChunkEnv) ext

/-- Tight exact-envelope (`Ct2SampledSendCt2ChunkEnv`) `<Ct2Sampled>::send_ct2_chunk` (Block `354`) on `spqrSendPlacedProg ext`. -/
abbrev Ct2SampledSendCt2ChunkTightPlacedOkX
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim F Ct2SampledSendCt2ChunkEnv ext

/-- `withVmPreserved`-wrapped `signal_session_coins_fill` (Block `618`) on `spqrSendPlacedProg ext`. -/
def CoinsFillPlacedOkX (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 618)
    (withLsCodeRoLoaded lsmpl (spqrCoinsFillSpecPlaced spqrSendCalleeStack))

/-! ## 3. Complete Relocatable Callee Contract Bundles for Block `427` -/

/-- Envelope-parametric bundle of all relocatable `[LibsignalPlacement]` callee contracts required by
    `spqr::send::<signal_session_ratchet::Coins>` (Block `427`). -/
structure SpqrSendPlacedContractsOfEnv (M : AllocCostModel)
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (EnvDecode : DecodeStateGhost → List AllocEvent → Prop)
    (EnvFromPb : StatesFromPbGhost → List AllocEvent → Prop)
    (EnvIntoPb : StatesIntoPbGhost C.F → List AllocEvent → Prop)
    (EnvMsgSer : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop)
    (PreEnvEncBytes PostEnvEncBytes : EncodeBytesGhost → List AllocEvent → Prop)
    (EnvNextChunk : PolyNextChunkGhost → List AllocEvent → Prop)
    (EnvHsEk : HeaderSentSendEkChunkGhost C.F → List AllocEvent → Prop)
    (EnvCt1rEk : Ct1ReceivedSendEkChunkGhost C.F → List AllocEvent → Prop)
    (EnvCt1sCt1 : Ct1SampledSendCt1ChunkGhost C.F → List AllocEvent → Prop)
    (EnvEkrCt1 : EkReceivedCt1SampledSendCt1ChunkGhost C.F → List AllocEvent → Prop)
    (EnvCt2sCt2 : Ct2SampledSendCt2ChunkGhost C.F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop where
  /-- Bridge between `DecodeState.optProtoInnerStateAt H_inner` and `Drop.optProtoInnerStateAt`. -/
  h_inner_eq :
    ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a st
  /-- Budget-threaded Rust heap allocator + `memcpy` + `memset` contracts under `[LibsignalPlacement]`. -/
  alloc : AllocContractsPlaced M A lim ext
  /-- `signal_session_coins_fill` (Block `618`). -/
  coinsFill_ok : CoinsFillPlacedOkX ext
  /-- `spqr::decode_state` (Block `325`). -/
  decodeState_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecXOfEnv H_inner M A lim EnvDecode))
  /-- `<States>::from_pb` (Block `333`). -/
  statesFromPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecXOfEnv M A lim C.F EnvFromPb))
  /-- `<States>::into_pb` (Block `334`). -/
  statesIntoPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim C.F EnvIntoPb))
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
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi M A lim EnvMsgSer))
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
  encodeBytes_ok : EncodeBytesPlacedOkXOfEnv PreEnvEncBytes PostEnvEncBytes A lim ext
  /-- `<PolyEncoder as Encoder>::next_chunk` (Block `416`). -/
  polyNextChunk_ok : PolyNextChunkPlacedOkXOfEnv EnvNextChunk M A lim ext
  /-- Leaf `<HeaderSent>::send_ek_chunk` (Block `336`). -/
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkPlacedOkXOfEnv M A lim C.F EnvHsEk ext
  /-- Leaf `<Ct1Received>::send_ek_chunk` (Block `345`). -/
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkPlacedOkXOfEnv M A lim C.F EnvCt1rEk ext
  /-- Leaf `<Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkPlacedOkXOfEnv M A lim C.F EnvCt1sCt1 ext
  /-- Leaf `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
  ekReceivedCt1SampledSendCt1Chunk_ok :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkXOfEnv M A lim C.F EnvEkrCt1 ext
  /-- Leaf `<Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkPlacedOkXOfEnv M A lim C.F EnvCt2sCt2 ext
  /-- `drop_glue::<proto::Chain> [local#2]` (Block `439`, CGU-local CLI counterpart of Block `136`). -/
  dropProtoChain_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim))
  /-- `drop_glue::<[chain::ChainEpoch]> [local#3]` (Block `446`, CGU-local CLI counterpart of Block `143`). -/
  dropChainEpochSlice_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec M A lim))

/-- Default relocatable `[LibsignalPlacement]` callee contract bundle for
    `spqr::send::<signal_session_ratchet::Coins>` (Block `427`), matching
    `SeamSpecsPlacedBudget.CliSpqrSendPeerSeams` 1-for-1. -/
abbrev SpqrSendPlacedContracts (M : AllocCostModel)
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  SpqrSendPlacedContractsOfEnv M H_inner A lim ctl C K
    DecodeStatePlacedEnv StatesFromPbEnv StatesIntoPbEnv MessageSerializeEnv
    (fun x => EncodeBytesEnv x.msg.length) (fun x => EncodeBytesEnv x.msg.length)
    PolyNextChunkEnv
    (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv)
    (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv) ext

/-- Tight exact-envelope relocatable `[LibsignalPlacement]` callee contract bundle for
    `spqr::send::<signal_session_ratchet::Coins>` (Block `427`), pairing `SpecsPlacedBudget`'s
    `spqrDecodeStatePlacedSpec`, `States.FromPb.DefsBudget.statesFromPbPlacedSpecX`, and
    `States.Leaves.DefsPlacedBudget`'s exact `*Send*ChunkEnv` leaf contracts. -/
structure SpqrSendPlacedContractsTight (M : AllocCostModel)
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  /-- Bridge between `DecodeState.optProtoInnerStateAt H_inner` and `Drop.optProtoInnerStateAt`. -/
  h_inner_eq :
    ∀ a st,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a st =
        CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a st
  /-- Budget-threaded Rust heap allocator + `memcpy` + `memset` contracts under `[LibsignalPlacement]`. -/
  alloc : AllocContractsPlaced M A lim ext
  /-- `signal_session_coins_fill` (Block `618`). -/
  coinsFill_ok : CoinsFillPlacedOkX ext
  /-- `spqr::decode_state` (Block `325`, `SpecsPlacedBudget.spqrDecodeStatePlacedSpec`). -/
  decodeState_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A lim))
  /-- `<States>::from_pb` (Block `333`, `States.FromPb.DefsBudget.statesFromPbPlacedSpecX`). -/
  statesFromPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX M A lim C.F))
  /-- `<States>::into_pb` (Block `334`). -/
  statesIntoPb_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim C.F))
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
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim))
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
  encodeBytes_ok : EncodeBytesPlacedOkX A lim ext
  /-- `<PolyEncoder as Encoder>::next_chunk` (Block `416`). -/
  polyNextChunk_ok : PolyNextChunkPlacedOkX M A lim ext
  /-- Tight leaf `<HeaderSent>::send_ek_chunk` (Block `336`). -/
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkTightPlacedOkX M A lim C.F ext
  /-- Tight leaf `<Ct1Received>::send_ek_chunk` (Block `345`). -/
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkTightPlacedOkX M A lim C.F ext
  /-- Tight leaf `<Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkTightPlacedOkX M A lim C.F ext
  /-- Tight leaf `<EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
  ekReceivedCt1SampledSendCt1Chunk_ok :
    EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX M A lim C.F ext
  /-- Tight leaf `<Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkTightPlacedOkX M A lim C.F ext
  /-- `drop_glue::<proto::Chain> [local#2]` (Block `439`). -/
  dropProtoChain_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim))
  /-- `drop_glue::<[chain::ChainEpoch]> [local#3]` (Block `446`). -/
  dropChainEpochSlice_ok :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec M A lim))

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
