/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget

/-!
# Guarded-Tight Leaf Merge Contracts and Bridges for `spqr::decode_state` (`Block 325`)

Defines `maxOps`-parametric `SpqrTightEvs` envelopes, canonical protobuf field-size guards
(`tlb_*Dom`), zero-capacity precondition heap predicates (`tlb_*ZeroCapAt`), and placed subroutine
contracts (`tlb_*PlacedTightOkOf`) for all leaf and chunked `prost` `merge` blocks (`295..312`)
called by `spqr::decode_state` (`Block 325`). Under `tlb_GuardedEnv Dom Tight Fallback`, canonical
inputs satisfy the tight small-class envelopes (`1,294,333 ≤ 1,307,216` cumulative bytes across Tags
1–3, `maxReq = 79,236`), while malformed inputs fall back to the untightened `*MergePostEnv` specs.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionLib lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainEpochPB ChainPB ChainParamsPB EpochDirectionPB MlKem PolynomialDecoder
   PolynomialEncoder PqRatchetState ProtoAuthenticator ProtoPolynomialDecoder
   ProtoPolynomialEncoder V1State VersionNegotiationPB spqrV1Init)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState encodeVarint mergeMessage)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk bytesMergeCapOk_zero sliceCursorAfter sliceCursorAt)
open CryptoVerification.SpqrV1.Auth (AuthMergeGhost authMergeStack authenticatorPBCapAt)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialDecoderGhost ProtoPolynomialEncoderGhost
   protoPolynomialDecoderAt protoPolynomialDecoderPinnedAt
   protoPolynomialEncoderAt protoPolynomialEncoderPinnedAt
   protoPolynomialEncoderPolysOff vecVecU8At vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr
  (authenticatorPBAt ct1SentPBAt ekSentCt1ReceivedPBAt epochDirectionPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1AcknowledgedMergeGhost ChunkedCt1ReceivedMergeGhost ChunkedCt1SampledMergeGhost
   ChunkedCt2SampledMergeGhost ChunkedEkReceivedCt1SampledMergeGhost
   ChunkedEkSentCt1ReceivedMergeGhost ChunkedHeaderReceivedMergeGhost ChunkedHeaderSentMergeGhost
   ChunkedKeysSampledMergeGhost ChunkedKeysUnsampledMergeGhost ChunkedNoHeaderReceivedMergeGhost
   PolyDecoderMergeGhost PolyEncoderMergeGhost V1StateMergeGhost codecWireTypeToProto
   optAuthenticatorPBCapAt polyDecoderToProto polyEncoderToProto polyMergeStack
   unchunkedCt1SentPBCapAt unchunkedEkSentCt1ReceivedPBCapAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost UnchunkedEkSentCt1ReceivedMergeGhost unchunkedMergeStack)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost EpochDirectionMergeGhost V1InnerHeapPred epochDirectionMergeStack
   epochDirectionPBCapOkAt vecU8CapOkAt)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (SpqrTightEvs SpqrTightHyps spqrTightEvs_fine_phaseCreditSpec spqrTightEvs_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (decodeStateTightDeltaCum decodeStateTightDeltaLive decodeStateTightDeltaPeak
   decodeStateTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (SpqrStateTight640 topStateTight_spqrV1Init)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (AuthMergeEnv authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1AcknowledgedMergeEnv ChunkedCt1ReceivedMergeEnv ChunkedCt1SampledMergeEnv
   ChunkedEkSentCt1ReceivedMergeEnv UnchunkedCt1SentMergeEnv UnchunkedEkSentCt1ReceivedMergeEnv
   chunkedCt1AcknowledgedMergeSpecOfEnv chunkedCt1ReceivedMergeSpecOfEnv
   chunkedCt1SampledMergeSpecOfEnv chunkedEkSentCt1ReceivedMergeSpecOfEnv
   unchunkedCt1SentMergeSpecOfEnv unchunkedEkSentCt1ReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedCt2SampledMergeEnv ChunkedEkReceivedCt1SampledMergeEnv ChunkedHeaderReceivedMergeEnv
   ChunkedHeaderSentMergeEnv ChunkedKeysSampledMergeEnv ChunkedKeysUnsampledMergeEnv
   ChunkedNoHeaderReceivedMergeEnv chunkedCt2SampledMergeSpecOfEnv
   chunkedEkReceivedCt1SampledMergeSpecOfEnv chunkedHeaderReceivedMergeSpecOfEnv
   chunkedHeaderSentMergeSpecOfEnv chunkedKeysSampledMergeSpecOfEnv
   chunkedKeysUnsampledMergeSpecOfEnv chunkedNoHeaderReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergeEnv PolyEncoderMergeEnv polyDecoderMergeSpecOfEnv polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv EpochDirectionMergeEnv epochDirectionMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX DecodeStatePlacedOkOfEnv
   spqrDecodeStatePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (nonFreeCount)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (bytesMerge3RawBudgetSpec)

/-! ## Guarded-Envelope Combinator and Length-Prefixed Wire Helper -/

/-- Guarded envelope combinator enforcing `Tight evs` when `Dom x` holds and `Fallback x evs` otherwise.
-/
def tlb_GuardedEnv {α : Type} (Dom : α → Prop)
    (Tight : List AllocEvent → Prop) (Fallback : α → List AllocEvent → Prop)
    (x : α) (evs : List AllocEvent) : Prop :=
  (Dom x ∧ Tight evs) ∨ (¬ Dom x ∧ Fallback x evs)

theorem tlb_guardedEnv_tight_of_dom {α : Type} {Dom : α → Prop}
    {Tight : List AllocEvent → Prop} {Fallback : α → List AllocEvent → Prop}
    {x : α} {evs : List AllocEvent}
    (hDom : Dom x) (h : tlb_GuardedEnv Dom Tight Fallback x evs) :
    Tight evs := by
  rcases h with ⟨_, ht⟩ | ⟨hnot, _⟩
  · exact ht
  · exact absurd hDom hnot

theorem tlb_fitsEnv_guarded_of_dom {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {α : Type} {Dom : α → Prop} {Tight : List AllocEvent → Prop}
    {Fallback : α → List AllocEvent → Prop} {x : α}
    (hDom : Dom x) (hFit : FitsEnv M lim st Tight) :
    FitsEnv M lim st (tlb_GuardedEnv Dom Tight Fallback x) :=
  fun evs h => hFit evs (tlb_guardedEnv_tight_of_dom hDom h)

theorem tlb_fitsEnv_fallback_of_not_dom {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {α : Type} {Dom : α → Prop} {Tight : List AllocEvent → Prop}
    {Fallback : α → List AllocEvent → Prop} {x : α}
    (hNot : ¬ Dom x) (hFit : FitsEnv M lim st (tlb_GuardedEnv Dom Tight Fallback x)) :
    FitsEnv M lim st (Fallback x) :=
  fun evs hf => hFit evs (Or.inr ⟨hNot, hf⟩)

/-- Length-prefixed wire slice passed to `prost::encoding::message::merge` after `decode_key`. -/
def tlb_lenPrefixed (raw rest : Bytes) : Bytes :=
  encodeVarint (BitVec.ofNat 64 raw.length) ++ raw ++ rest

/-! ## Canonical Field-Size Predicates on Protobuf Structures -/

def tlb_ValidAuthPB (m : ProtoAuthenticator) : Prop :=
  m.rootKey.length ≤ 32 ∧ m.macKey.length ≤ 32

def tlb_ValidOptAuthPB (a : Option ProtoAuthenticator) : Prop :=
  ∀ v, a = some v → tlb_ValidAuthPB v

def tlb_ValidPolyDecoderPB (m : PolynomialDecoder) : Prop :=
  m.pts.length ≤ 16 ∧ ∀ s ∈ m.pts, s.length ≤ 2560

def tlb_ValidPolyEncoderPB (m : PolynomialEncoder) : Prop :=
  (m.pts = [] ∨ m.polys = []) ∧
  m.pts.length + m.polys.length ≤ 16 ∧
  (∀ s ∈ m.pts, s.length ≤ 2560) ∧
  (∀ s ∈ m.polys, s.length ≤ 2560)

def tlb_ValidUcKeysUnsampledPB (m : V1State.Unchunked.KeysUnsampled) : Prop :=
  tlb_ValidOptAuthPB m.auth

def tlb_ValidUcHeaderSentPB (m : V1State.Unchunked.HeaderSent) : Prop :=
  tlb_ValidOptAuthPB m.auth ∧ m.ek.length ≤ 1152 ∧ m.dk.length ≤ 2400

def tlb_ValidUcEkSentPB (m : V1State.Unchunked.EkSent) : Prop :=
  tlb_ValidOptAuthPB m.auth ∧ m.dk.length ≤ 2400

def tlb_ValidUcEkSentCt1ReceivedPB (m : V1State.Unchunked.EkSentCt1Received) : Prop :=
  tlb_ValidOptAuthPB m.auth ∧ m.dk.length ≤ 2400 ∧ m.ct1.length ≤ 960

def tlb_ValidUcNoHeaderReceivedPB (m : V1State.Unchunked.NoHeaderReceived) : Prop :=
  tlb_ValidOptAuthPB m.auth

def tlb_ValidUcHeaderReceivedPB (m : V1State.Unchunked.HeaderReceived) : Prop :=
  tlb_ValidOptAuthPB m.auth ∧ m.hdr.length ≤ 64

def tlb_ValidUcCt1SentPB (m : V1State.Unchunked.Ct1Sent) : Prop :=
  tlb_ValidOptAuthPB m.auth ∧ m.hdr.length ≤ 64 ∧ m.es.length ≤ 2080 ∧ m.ct1.length ≤ 960

def tlb_ValidUcCt1SentEkReceivedPB (m : V1State.Unchunked.Ct1SentEkReceived) : Prop :=
  tlb_ValidOptAuthPB m.auth ∧ m.es.length ≤ 2080 ∧ m.ek.length ≤ 1152 ∧ m.ct1.length ≤ 960

def tlb_ValidUcCt2SentPB (m : V1State.Unchunked.Ct2Sent) : Prop :=
  tlb_ValidOptAuthPB m.auth

def tlb_ValidChunkedKeysUnsampledPB (m : V1State.Chunked.KeysUnsampled) : Prop :=
  ∀ u, m.uc = some u → tlb_ValidUcKeysUnsampledPB u

def tlb_ValidChunkedKeysSampledPB (m : V1State.Chunked.KeysSampled) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcHeaderSentPB u) ∧
  (∀ e, m.sendingHdr = some e → tlb_ValidPolyEncoderPB e)

def tlb_ValidChunkedHeaderSentPB (m : V1State.Chunked.HeaderSent) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcEkSentPB u) ∧
  (∀ e, m.sendingEk = some e → tlb_ValidPolyEncoderPB e) ∧
  (∀ d, m.receivingCt1 = some d → tlb_ValidPolyDecoderPB d)

def tlb_ValidChunkedCt1ReceivedPB (m : V1State.Chunked.Ct1Received) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcEkSentCt1ReceivedPB u) ∧
  (∀ e, m.sendingEk = some e → tlb_ValidPolyEncoderPB e)

def tlb_ValidChunkedEkSentCt1ReceivedPB (m : V1State.Chunked.EkSentCt1Received) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcEkSentCt1ReceivedPB u) ∧
  (∀ d, m.receivingCt2 = some d → tlb_ValidPolyDecoderPB d)

def tlb_ValidChunkedNoHeaderReceivedPB (m : V1State.Chunked.NoHeaderReceived) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcNoHeaderReceivedPB u) ∧
  (∀ d, m.receivingHdr = some d → tlb_ValidPolyDecoderPB d)

def tlb_ValidChunkedHeaderReceivedPB (m : V1State.Chunked.HeaderReceived) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcHeaderReceivedPB u) ∧
  (∀ d, m.receivingEk = some d → tlb_ValidPolyDecoderPB d)

def tlb_ValidChunkedCt1SampledPB (m : V1State.Chunked.Ct1Sampled) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcCt1SentPB u) ∧
  (∀ e, m.sendingCt1 = some e → tlb_ValidPolyEncoderPB e) ∧
  (∀ d, m.receivingEk = some d → tlb_ValidPolyDecoderPB d)

def tlb_ValidChunkedEkReceivedCt1SampledPB (m : V1State.Chunked.EkReceivedCt1Sampled) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcCt1SentEkReceivedPB u) ∧
  (∀ e, m.sendingCt1 = some e → tlb_ValidPolyEncoderPB e)

def tlb_ValidChunkedCt1AcknowledgedPB (m : V1State.Chunked.Ct1Acknowledged) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcCt1SentPB u) ∧
  (∀ d, m.receivingEk = some d → tlb_ValidPolyDecoderPB d)

def tlb_ValidChunkedCt2SampledPB (m : V1State.Chunked.Ct2Sampled) : Prop :=
  (∀ u, m.uc = some u → tlb_ValidUcCt2SentPB u) ∧
  (∀ e, m.sendingCt2 = some e → tlb_ValidPolyEncoderPB e)

def tlb_ValidInnerStatePB : V1State.InnerState → Prop
  | .keysUnsampled v        => tlb_ValidChunkedKeysUnsampledPB v
  | .keysSampled v          => tlb_ValidChunkedKeysSampledPB v
  | .headerSent v           => tlb_ValidChunkedHeaderSentPB v
  | .ct1Received v          => tlb_ValidChunkedCt1ReceivedPB v
  | .ekSentCt1Received v    => tlb_ValidChunkedEkSentCt1ReceivedPB v
  | .noHeaderReceived v     => tlb_ValidChunkedNoHeaderReceivedPB v
  | .headerReceived v       => tlb_ValidChunkedHeaderReceivedPB v
  | .ct1Sampled v           => tlb_ValidChunkedCt1SampledPB v
  | .ekReceivedCt1Sampled v => tlb_ValidChunkedEkReceivedCt1SampledPB v
  | .ct1Acknowledged v      => tlb_ValidChunkedCt1AcknowledgedPB v
  | .ct2Sampled v           => tlb_ValidChunkedCt2SampledPB v

def tlb_ValidV1StatePB (m : V1State) : Prop :=
  ∀ is, m.innerState = some is → tlb_ValidInnerStatePB is

def tlb_ValidEpochDirPB (maxPrev : Nat) (m : EpochDirectionPB) : Prop :=
  m.next.length ≤ 32 ∧ m.prev.length ≤ maxPrev

def tlb_ValidChainEpochPB (m : ChainEpochPB) : Prop :=
  (∀ d, m.send = some d → tlb_ValidEpochDirPB 0 d) ∧
  (∀ d, m.recv = some d → tlb_ValidEpochDirPB 79236 d)

def tlb_ValidChainPB (m : ChainPB) : Prop :=
  m.links.length ≤ 3 ∧
  m.nextRoot.length ≤ 32 ∧
  ∀ ep ∈ m.links, tlb_ValidChainEpochPB ep

def tlb_ValidVersionNegotiationPB (m : VersionNegotiationPB) : Prop :=
  m.authKey.length ≤ 32

def tlb_ValidPqRatchetStatePB (m : PqRatchetState) : Prop :=
  (∀ vn, m.versionNegotiation = some vn → tlb_ValidVersionNegotiationPB vn) ∧
  (∀ ch, m.chain = some ch → tlb_ValidChainPB ch) ∧
  (∀ v1, m.inner = some (.v1 v1) → tlb_ValidV1StatePB v1)

/-! ## Per-Block `maxOps`-Parametric Tight Envelopes -/

/-- Tight envelope for Block `295` (`ProtoAuthenticator::merge`: `2,952` bytes, `maxReq = 32`). -/
def tlb_AuthTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 2952 32
abbrev tlb_AuthTightEnv : List AllocEvent → Prop := tlb_AuthTightEnvOf 4

/-- Tight envelope for Block `296` (`PolynomialDecoder::merge`: `342,615` bytes, `maxReq = 2,560`).
-/
def tlb_PolyDecoderTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 342615 2560
abbrev tlb_PolyDecoderTightEnv : List AllocEvent → Prop := tlb_PolyDecoderTightEnvOf 35

/-- Tight envelope for Block `297` (`PolynomialEncoder::merge`: `342,615` bytes, `maxReq = 2,560`).
-/
def tlb_PolyEncoderTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 342615 2560
abbrev tlb_PolyEncoderTightEnv : List AllocEvent → Prop := tlb_PolyEncoderTightEnvOf 35

/-- Tight envelope for Block `299` (`EpochDirectionPB::merge`, send direction: `1,476` bytes, `maxReq = 32`).
-/
def tlb_EpochDirSendTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 1476 32
abbrev tlb_EpochDirSendTightEnv : List AllocEvent → Prop := tlb_EpochDirSendTightEnvOf 2

/-- Tight envelope for Block `299` (`EpochDirectionPB::merge`, recv direction: `181,944` bytes, `maxReq = 79,236`).
-/
def tlb_EpochDirRecvTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 181944 79236
abbrev tlb_EpochDirRecvTightEnv : List AllocEvent → Prop := tlb_EpochDirRecvTightEnvOf 4

/-- Tight envelope for Block `311` (`Unchunked.EkSentCt1Received::merge`: `42,108` bytes, `maxReq = 2,560`).
-/
def tlb_UcEkSentCt1ReceivedTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 42108 2560
abbrev tlb_UcEkSentCt1ReceivedTightEnv : List AllocEvent → Prop := tlb_UcEkSentCt1ReceivedTightEnvOf 8

/-- Tight envelope for Block `312` (`Unchunked.Ct1Sent::merge`: `46,102` bytes, `maxReq = 2,560`).
-/
def tlb_UcCt1SentTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 46102 2560
abbrev tlb_UcCt1SentTightEnv : List AllocEvent → Prop := tlb_UcCt1SentTightEnvOf 10

/-- Tight envelope for Block `300` (`Chunked.Ct1Sampled::merge`: `731,332` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedCt1SampledTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 731332 2560
abbrev tlb_ChunkedCt1SampledTightEnv : List AllocEvent → Prop := tlb_ChunkedCt1SampledTightEnvOf 80

/-- Tight envelope for Block `301` (`Chunked.Ct2Sampled::merge`: `345,567` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedCt2SampledTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 345567 2560
abbrev tlb_ChunkedCt2SampledTightEnv : List AllocEvent → Prop := tlb_ChunkedCt2SampledTightEnvOf 39

/-- Tight envelope for Block `302` (`Chunked.HeaderSent::merge`: `707,760` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedHeaderSentTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 707760 2560
abbrev tlb_ChunkedHeaderSentTightEnv : List AllocEvent → Prop := tlb_ChunkedHeaderSentTightEnvOf 76

/-- Tight envelope for Block `303` (`Chunked.Ct1Received::merge`: `384,723` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedCt1ReceivedTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 384723 2560
abbrev tlb_ChunkedCt1ReceivedTightEnv : List AllocEvent → Prop := tlb_ChunkedCt1ReceivedTightEnvOf 43

/-- Tight envelope for Block `304` (`Chunked.KeysSampled::merge`: `384,723` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedKeysSampledTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 384723 2560
abbrev tlb_ChunkedKeysSampledTightEnv : List AllocEvent → Prop := tlb_ChunkedKeysSampledTightEnvOf 43

/-- Tight envelope for Block `305` (`Chunked.KeysUnsampled::merge`: `2,952` bytes, `maxReq = 32`).
-/
def tlb_ChunkedKeysUnsampledTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 2952 32
abbrev tlb_ChunkedKeysUnsampledTightEnv : List AllocEvent → Prop := tlb_ChunkedKeysUnsampledTightEnvOf 4

/-- Tight envelope for Block `306` (`Chunked.HeaderReceived::merge`: `349,561` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedHeaderReceivedTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 349561 2560
abbrev tlb_ChunkedHeaderReceivedTightEnv : List AllocEvent → Prop := tlb_ChunkedHeaderReceivedTightEnvOf 41

/-- Tight envelope for Block `307` (`Chunked.Ct1Acknowledged::merge`: `388,717` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedCt1AcknowledgedTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 388717 2560
abbrev tlb_ChunkedCt1AcknowledgedTightEnv : List AllocEvent → Prop := tlb_ChunkedCt1AcknowledgedTightEnvOf 45

/-- Tight envelope for Block `308` (`Chunked.NoHeaderReceived::merge`: `345,567` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedNoHeaderReceivedTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 345567 2560
abbrev tlb_ChunkedNoHeaderReceivedTightEnv : List AllocEvent → Prop := tlb_ChunkedNoHeaderReceivedTightEnvOf 39

/-- Tight envelope for Block `309` (`Chunked.EkSentCt1Received::merge`: `384,723` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedEkSentCt1ReceivedTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 384723 2560
abbrev tlb_ChunkedEkSentCt1ReceivedTightEnv : List AllocEvent → Prop := tlb_ChunkedEkSentCt1ReceivedTightEnvOf 43

/-- Tight envelope for Block `310` (`Chunked.EkReceivedCt1Sampled::merge`: `404,301` bytes, `maxReq = 2,560`).
-/
def tlb_ChunkedEkReceivedCt1SampledTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 404301 2560
abbrev tlb_ChunkedEkReceivedCt1SampledTightEnv : List AllocEvent → Prop := tlb_ChunkedEkReceivedCt1SampledTightEnvOf 45

/-- Tight envelope for Block `298` (`V1State::merge`: `731,332` bytes, `maxReq = 2,560`). -/
def tlb_V1StateMergeTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 731332 2560
abbrev tlb_V1StateMergeTightEnv : List AllocEvent → Prop := tlb_V1StateMergeTightEnvOf 80

/-- Tight envelope for Block `325` (`spqr::decode_state`: `SpqrTightEvs maxOps 1307216 79236`). -/
def tlb_DecodeStateTightEnvOf (maxOps : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs maxOps 1307216 79236
abbrev tlb_DecodeStateTightEnv : List AllocEvent → Prop := tlb_DecodeStateTightEnvOf 109

/-- Tight envelope for Block `325` Tag 1 (`VersionNegotiationPB`: `1,476` bytes, `maxReq = 32`). -/
def tlb_DecodeStateTag1TightEnvOf (tag1Ops : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs tag1Ops 1476 32
abbrev tlb_DecodeStateTag1TightEnv : List AllocEvent → Prop := tlb_DecodeStateTag1TightEnvOf 2

/-- Tight envelope for Block `325` Tag 2 (`ChainPB`: `561,525` bytes, `maxReq = 79,236`). -/
def tlb_DecodeStateTag2TightEnvOf (tag2Ops : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs tag2Ops 561525 79236
abbrev tlb_DecodeStateTag2TightEnv : List AllocEvent → Prop := tlb_DecodeStateTag2TightEnvOf 21

/-- Tight envelope for Block `325` Tag 3 (`PqRatchetInner::V1`: `731,332` bytes, `maxReq = 2,560`).
-/
def tlb_DecodeStateTag3TightEnvOf (v1Ops : Nat) : List AllocEvent → Prop :=
  SpqrTightEvs v1Ops 731332 2560
abbrev tlb_DecodeStateTag3TightEnv : List AllocEvent → Prop := tlb_DecodeStateTag3TightEnvOf 80

/-- Arithmetic reconciliation of Tag 1–3 cumulative bytes (`1,294,333 ≤ 1,307,216`) and operation counts (`103 ≤ 109 ≤ 128`).
-/
theorem tlb_decodeState_budget_reconcile_arith :
    1476 + 561525 + 731332 ≤ 1307216 ∧
    9789 + 1476 + 3 * (1476 + 181944) = 561525 ∧
    1 + 2 + 3 * (2 + 4) = 21 ∧
    2 + 21 + 80 = 103 ∧
    103 ≤ 109 ∧
    109 ≤ 128 := by
  decide

/-- Composes Tag 1–3 `SpqrTightEvs` bounds into `tlb_DecodeStateTightEnvOf maxOps`. -/
theorem tlb_decodeState_tags_compose {t1 t2 v1Ops maxOps : Nat}
    {evs1 evs2 evs3 : List AllocEvent}
    (hOps : t1 + t2 + v1Ops ≤ maxOps)
    (h1 : tlb_DecodeStateTag1TightEnvOf t1 evs1)
    (h2 : tlb_DecodeStateTag2TightEnvOf t2 evs2)
    (h3 : tlb_DecodeStateTag3TightEnvOf v1Ops evs3) :
    tlb_DecodeStateTightEnvOf maxOps (evs1 ++ evs2 ++ evs3) :=
  ((SpqrTightEvs.append h1 h2).append h3).mono hOps (by decide) (by decide)

/-! ## Per-Block Canonical Input Guards (`tlb_*Dom`) and Guarded Envelopes -/

def tlb_AuthDom (x : AuthMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidAuthPB pb ∧ x.bs = tlb_lenPrefixed (ProtoAuthenticator.encodeRaw pb) rest

def tlb_AuthGuardedEnvOf (maxOps : Nat) : AuthMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_AuthDom (tlb_AuthTightEnvOf maxOps) AuthMergeEnv
abbrev tlb_AuthGuardedEnv := tlb_AuthGuardedEnvOf 4

def tlb_PolyDecoderDom (x : PolyDecoderMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidPolyDecoderPB pb ∧ x.bs = tlb_lenPrefixed (PolynomialDecoder.encodeRaw pb) rest

def tlb_PolyDecoderGuardedEnvOf (maxOps : Nat) : PolyDecoderMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_PolyDecoderDom (tlb_PolyDecoderTightEnvOf maxOps) PolyDecoderMergeEnv
abbrev tlb_PolyDecoderGuardedEnv := tlb_PolyDecoderGuardedEnvOf 35

def tlb_PolyEncoderDom (x : PolyEncoderMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidPolyEncoderPB pb ∧ x.bs = tlb_lenPrefixed (PolynomialEncoder.encodeRaw pb) rest

def tlb_PolyEncoderGuardedEnvOf (maxOps : Nat) : PolyEncoderMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_PolyEncoderDom (tlb_PolyEncoderTightEnvOf maxOps) PolyEncoderMergeEnv
abbrev tlb_PolyEncoderGuardedEnv := tlb_PolyEncoderGuardedEnvOf 35

def tlb_EpochDirDom (maxPrev : Nat) (x : EpochDirectionMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidEpochDirPB maxPrev pb ∧ x.bs = tlb_lenPrefixed (EpochDirectionPB.encodeRaw pb) rest

/-- Unified guarded envelope for Block `299` (`EpochDirectionPB::merge`) covering both send (`maxPrev = 0`) and recv (`maxPrev = 79,236`) directions.
-/
def tlb_EpochDirectionGuardedEnvOf (sendOps recvOps : Nat)
    (x : EpochDirectionMergeGhost) (evs : List AllocEvent) : Prop :=
  (tlb_EpochDirDom 0 x ∧ tlb_EpochDirSendTightEnvOf sendOps evs) ∨
  (¬ tlb_EpochDirDom 0 x ∧ tlb_EpochDirDom 79236 x ∧ tlb_EpochDirRecvTightEnvOf recvOps evs) ∨
  (¬ tlb_EpochDirDom 79236 x ∧ EpochDirectionMergeEnv x evs)
abbrev tlb_EpochDirectionGuardedEnv := tlb_EpochDirectionGuardedEnvOf 2 4

def tlb_UcEkSentCt1ReceivedDom (x : UnchunkedEkSentCt1ReceivedMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidUcEkSentCt1ReceivedPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw pb) rest

def tlb_UcEkSentCt1ReceivedGuardedEnvOf (maxOps : Nat) :
    UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
    (tlb_UcEkSentCt1ReceivedTightEnvOf maxOps) UnchunkedEkSentCt1ReceivedMergeEnv
abbrev tlb_UcEkSentCt1ReceivedGuardedEnv := tlb_UcEkSentCt1ReceivedGuardedEnvOf 8

def tlb_UcCt1SentDom (x : UnchunkedCt1SentMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidUcCt1SentPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw pb) rest

def tlb_UcCt1SentGuardedEnvOf (maxOps : Nat) :
    UnchunkedCt1SentMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_UcCt1SentDom (tlb_UcCt1SentTightEnvOf maxOps) UnchunkedCt1SentMergeEnv
abbrev tlb_UcCt1SentGuardedEnv := tlb_UcCt1SentGuardedEnvOf 10

def tlb_ChunkedCt1SampledDom (x : ChunkedCt1SampledMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedCt1SampledPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.Ct1Sampled.encodeRaw pb) rest

def tlb_ChunkedCt1SampledGuardedEnvOf (maxOps : Nat) :
    ChunkedCt1SampledMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedCt1SampledDom
    (tlb_ChunkedCt1SampledTightEnvOf maxOps) ChunkedCt1SampledMergeEnv
abbrev tlb_ChunkedCt1SampledGuardedEnv := tlb_ChunkedCt1SampledGuardedEnvOf 80

def tlb_ChunkedCt2SampledDom (x : ChunkedCt2SampledMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedCt2SampledPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.Ct2Sampled.encodeRaw pb) rest

def tlb_ChunkedCt2SampledGuardedEnvOf (maxOps : Nat) :
    ChunkedCt2SampledMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedCt2SampledDom
    (tlb_ChunkedCt2SampledTightEnvOf maxOps) ChunkedCt2SampledMergeEnv
abbrev tlb_ChunkedCt2SampledGuardedEnv := tlb_ChunkedCt2SampledGuardedEnvOf 39

def tlb_ChunkedHeaderSentDom (x : ChunkedHeaderSentMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedHeaderSentPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.HeaderSent.encodeRaw pb) rest

def tlb_ChunkedHeaderSentGuardedEnvOf (maxOps : Nat) :
    ChunkedHeaderSentMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedHeaderSentDom
    (tlb_ChunkedHeaderSentTightEnvOf maxOps) ChunkedHeaderSentMergeEnv
abbrev tlb_ChunkedHeaderSentGuardedEnv := tlb_ChunkedHeaderSentGuardedEnvOf 76

def tlb_ChunkedCt1ReceivedDom (x : ChunkedCt1ReceivedMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedCt1ReceivedPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.Ct1Received.encodeRaw pb) rest

def tlb_ChunkedCt1ReceivedGuardedEnvOf (maxOps : Nat) :
    ChunkedCt1ReceivedMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedCt1ReceivedDom
    (tlb_ChunkedCt1ReceivedTightEnvOf maxOps) ChunkedCt1ReceivedMergeEnv
abbrev tlb_ChunkedCt1ReceivedGuardedEnv := tlb_ChunkedCt1ReceivedGuardedEnvOf 43

def tlb_ChunkedKeysSampledDom (x : ChunkedKeysSampledMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedKeysSampledPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.KeysSampled.encodeRaw pb) rest

def tlb_ChunkedKeysSampledGuardedEnvOf (maxOps : Nat) :
    ChunkedKeysSampledMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedKeysSampledDom
    (tlb_ChunkedKeysSampledTightEnvOf maxOps) ChunkedKeysSampledMergeEnv
abbrev tlb_ChunkedKeysSampledGuardedEnv := tlb_ChunkedKeysSampledGuardedEnvOf 43

def tlb_ChunkedKeysUnsampledDom (x : ChunkedKeysUnsampledMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedKeysUnsampledPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.KeysUnsampled.encodeRaw pb) rest

def tlb_ChunkedKeysUnsampledGuardedEnvOf (maxOps : Nat) :
    ChunkedKeysUnsampledMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedKeysUnsampledDom
    (tlb_ChunkedKeysUnsampledTightEnvOf maxOps) ChunkedKeysUnsampledMergeEnv
abbrev tlb_ChunkedKeysUnsampledGuardedEnv := tlb_ChunkedKeysUnsampledGuardedEnvOf 4

def tlb_ChunkedHeaderReceivedDom (x : ChunkedHeaderReceivedMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedHeaderReceivedPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.HeaderReceived.encodeRaw pb) rest

def tlb_ChunkedHeaderReceivedGuardedEnvOf (maxOps : Nat) :
    ChunkedHeaderReceivedMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedHeaderReceivedDom
    (tlb_ChunkedHeaderReceivedTightEnvOf maxOps) ChunkedHeaderReceivedMergeEnv
abbrev tlb_ChunkedHeaderReceivedGuardedEnv := tlb_ChunkedHeaderReceivedGuardedEnvOf 41

def tlb_ChunkedCt1AcknowledgedDom (x : ChunkedCt1AcknowledgedMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedCt1AcknowledgedPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.Ct1Acknowledged.encodeRaw pb) rest

def tlb_ChunkedCt1AcknowledgedGuardedEnvOf (maxOps : Nat) :
    ChunkedCt1AcknowledgedMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedCt1AcknowledgedDom
    (tlb_ChunkedCt1AcknowledgedTightEnvOf maxOps) ChunkedCt1AcknowledgedMergeEnv
abbrev tlb_ChunkedCt1AcknowledgedGuardedEnv := tlb_ChunkedCt1AcknowledgedGuardedEnvOf 45

def tlb_ChunkedNoHeaderReceivedDom (x : ChunkedNoHeaderReceivedMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedNoHeaderReceivedPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.NoHeaderReceived.encodeRaw pb) rest

def tlb_ChunkedNoHeaderReceivedGuardedEnvOf (maxOps : Nat) :
    ChunkedNoHeaderReceivedMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedNoHeaderReceivedDom
    (tlb_ChunkedNoHeaderReceivedTightEnvOf maxOps) ChunkedNoHeaderReceivedMergeEnv
abbrev tlb_ChunkedNoHeaderReceivedGuardedEnv := tlb_ChunkedNoHeaderReceivedGuardedEnvOf 39

def tlb_ChunkedEkSentCt1ReceivedDom (x : ChunkedEkSentCt1ReceivedMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedEkSentCt1ReceivedPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.EkSentCt1Received.encodeRaw pb) rest

def tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf (maxOps : Nat) :
    ChunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedEkSentCt1ReceivedDom
    (tlb_ChunkedEkSentCt1ReceivedTightEnvOf maxOps) ChunkedEkSentCt1ReceivedMergeEnv
abbrev tlb_ChunkedEkSentCt1ReceivedGuardedEnv := tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf 43

def tlb_ChunkedEkReceivedCt1SampledDom (x : ChunkedEkReceivedCt1SampledMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, tlb_ValidChunkedEkReceivedCt1SampledPB pb ∧
      x.bs = tlb_lenPrefixed (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw pb) rest

def tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf (maxOps : Nat) :
    ChunkedEkReceivedCt1SampledMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedEkReceivedCt1SampledDom
    (tlb_ChunkedEkReceivedCt1SampledTightEnvOf maxOps) ChunkedEkReceivedCt1SampledMergeEnv
abbrev tlb_ChunkedEkReceivedCt1SampledGuardedEnv := tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf 45

def tlb_V1StateMergeDom (x : V1StateMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg.innerState = none ∧
    ∃ pb rest, tlb_ValidV1StatePB pb ∧ x.bs = tlb_lenPrefixed (V1State.encodeRaw pb) rest

def tlb_V1StateMergeGuardedEnvOf (maxOps : Nat) : V1StateMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_V1StateMergeDom (tlb_V1StateMergeTightEnvOf maxOps) V1StateMergeEnv
abbrev tlb_V1StateMergeGuardedEnv := tlb_V1StateMergeGuardedEnvOf 80

/-!
## Zero-Capacity Guarded Leaf Preconditions and Placed Subroutine Contracts

Under `Dom x`, the non-`Option` leaf structs (`ProtoAuthenticator`, `ProtoPolynomialDecoder`,
`ProtoPolynomialEncoder`, `EpochDirectionPB`, `Unchunked.EkSentCt1Received`, `Unchunked.Ct1Sent`)
pin initial `Vec` capacities to `0#64` (matching `Option::none → Some(default)` initialization at
call sites), while falling back to unpinned representations under `¬ Dom x`.
-/

/-- Guarded precondition heap combinator selecting `ZeroAt x` under `Dom x` and `CapAt x` otherwise.
-/
noncomputable def tlb_domHeap {α : Type} (Dom : α → Prop)
    (ZeroAt CapAt : α → SepProp) (x : α) : SepProp :=
  open Classical in
  if Dom x then ZeroAt x else CapAt x

@[simp] theorem tlb_domHeap_of_dom {α : Type} {Dom : α → Prop} {ZeroAt CapAt : α → SepProp}
    {x : α} (h : Dom x) :
    tlb_domHeap Dom ZeroAt CapAt x = ZeroAt x := by
  simp [tlb_domHeap, h]

@[simp] theorem tlb_domHeap_of_not_dom {α : Type} {Dom : α → Prop} {ZeroAt CapAt : α → SepProp}
    {x : α} (h : ¬ Dom x) :
    tlb_domHeap Dom ZeroAt CapAt x = CapAt x := by
  simp [tlb_domHeap, h]

theorem tlb_domHeap_entails_cap {α : Type} {Dom : α → Prop} {ZeroAt CapAt : α → SepProp}
    (x : α) (hZero : ZeroAt x ⊢ CapAt x) :
    tlb_domHeap Dom ZeroAt CapAt x ⊢ CapAt x := by
  classical
  by_cases h : Dom x
  · rw [tlb_domHeap_of_dom h]
    exact hZero
  · rw [tlb_domHeap_of_not_dom h]
    exact Entails.refl _

theorem tlb_epochDirDom_zero_imp_79236 {x : EpochDirectionMergeGhost}
    (h : tlb_EpochDirDom 0 x) :
    tlb_EpochDirDom 79236 x := by
  rcases h with ⟨hwt, hmsg, pb, rest, ⟨hnext, hprev⟩, hbs⟩
  exact ⟨hwt, hmsg, pb, rest, ⟨hnext, Nat.le_trans hprev (Nat.zero_le _)⟩, hbs⟩

/-- Zero-capacity `Vec<u8>` at `v` (`cap = 0#64`). -/
def tlb_vecU8ZeroCapAt (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ ptr : BitVec 64, vecU8At A v 0#64 ptr bs

theorem tlb_vecU8ZeroCapAt_of_ptr (A : RustAlloc) (v ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v 0#64 ptr bs ⊢ tlb_vecU8ZeroCapAt A v bs :=
  Entails.sepExists_right ptr (Entails.refl _)

theorem tlb_vecU8ZeroCapAt_entails_cap (A : RustAlloc) (v : BitVec 64) (bsLen : Nat)
    (bs : List (BitVec 8)) :
    tlb_vecU8ZeroCapAt A v bs ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A v cap ptr bs) := by
  refine Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right ptr ?_)
  exact Entails.pure_right bytesMergeCapOk_zero (Entails.refl _)

theorem tlb_vecU8ZeroCapAt_entails_vecU8CapOkAt (A : RustAlloc) (v : BitVec 64) (remLen : Nat)
    (bs : List (BitVec 8)) :
    tlb_vecU8ZeroCapAt A v bs ⊢ vecU8CapOkAt A v remLen bs :=
  tlb_vecU8ZeroCapAt_entails_cap A v remLen bs

def tlb_authenticatorZeroCapAt (A : RustAlloc) (a : BitVec 64)
    (auth : ProtoAuthenticator) : SepProp :=
  tlb_vecU8ZeroCapAt A a auth.rootKey ∗
  tlb_vecU8ZeroCapAt A (a + 0x18#64) auth.macKey

theorem tlb_authenticatorZeroCapAt_entails_cap (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) :
    tlb_authenticatorZeroCapAt A a auth ⊢ authenticatorPBCapAt A a bsLen auth :=
  sepConj_mono (tlb_vecU8ZeroCapAt_entails_cap A a bsLen auth.rootKey)
    (tlb_vecU8ZeroCapAt_entails_cap A (a + 0x18#64) bsLen auth.macKey)

def tlb_optAuthZeroCapAt (A : RustAlloc) (a : BitVec 64) :
    Option ProtoAuthenticator → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => tlb_authenticatorZeroCapAt A a auth

theorem tlb_optAuthZeroCapAt_entails_cap (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    ∀ opt : Option ProtoAuthenticator,
      tlb_optAuthZeroCapAt A a opt ⊢ optAuthenticatorPBCapAt A a bsLen opt
  | none => Entails.refl _
  | some auth => tlb_authenticatorZeroCapAt_entails_cap A a bsLen auth

theorem tlb_vecVecU8ZeroPin_entails_unpinned (A : RustAlloc) (ptr v : BitVec 64)
    (bss : List (List (BitVec 8))) :
    vecVecU8PinnedAt A ⟨0#64, ptr⟩ v bss ⊢ vecVecU8At A v bss := by
  unfold vecVecU8PinnedAt vecVecU8At CryptoVerification.RustHeap.vecOf
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right ptr (Entails.refl _))

def tlb_polyDecoderZeroCapAt (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder) : SepProp :=
  ∃∗ ptr : BitVec 64, protoPolynomialDecoderPinnedAt A ⟨⟨0#64, ptr⟩⟩ a pb

theorem tlb_polyDecoderZeroCapAt_of_ptr (A : RustAlloc) (ptr a : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    protoPolynomialDecoderPinnedAt A ⟨⟨0#64, ptr⟩⟩ a pb ⊢ tlb_polyDecoderZeroCapAt A a pb :=
  Entails.sepExists_right ptr (Entails.refl _)

theorem tlb_polyDecoderZeroCapAt_entails_unpinned (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialDecoder) :
    tlb_polyDecoderZeroCapAt A a pb ⊢ protoPolynomialDecoderAt A a pb := by
  refine Entails.sepExists_elim fun ptr => ?_
  unfold protoPolynomialDecoderPinnedAt protoPolynomialDecoderAt
  exact sepConj_mono (tlb_vecVecU8ZeroPin_entails_unpinned A ptr a pb.pts) (Entails.refl _)

def tlb_polyEncoderZeroCapAt (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) : SepProp :=
  ∃∗ ptrPts : BitVec 64, ∃∗ ptrPolys : BitVec 64,
    protoPolynomialEncoderPinnedAt A ⟨⟨0#64, ptrPts⟩, ⟨0#64, ptrPolys⟩⟩ a pb

theorem tlb_polyEncoderZeroCapAt_of_ptrs (A : RustAlloc) (ptrPts ptrPolys a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    protoPolynomialEncoderPinnedAt A ⟨⟨0#64, ptrPts⟩, ⟨0#64, ptrPolys⟩⟩ a pb ⊢
      tlb_polyEncoderZeroCapAt A a pb :=
  Entails.sepExists_right ptrPts (Entails.sepExists_right ptrPolys (Entails.refl _))

theorem tlb_polyEncoderZeroCapAt_entails_unpinned (A : RustAlloc) (a : BitVec 64)
    (pb : ProtoPolynomialEncoder) :
    tlb_polyEncoderZeroCapAt A a pb ⊢ protoPolynomialEncoderAt A a pb := by
  refine Entails.sepExists_elim fun ptrPts => Entails.sepExists_elim fun ptrPolys => ?_
  unfold protoPolynomialEncoderPinnedAt protoPolynomialEncoderAt
  exact sepConj_mono (tlb_vecVecU8ZeroPin_entails_unpinned A ptrPts a pb.pts)
    (sepConj_mono
      (tlb_vecVecU8ZeroPin_entails_unpinned A ptrPolys (a + protoPolynomialEncoderPolysOff) pb.polys)
      (Entails.refl _))

def tlb_epochDirectionZeroCapAt (A : RustAlloc) (a : BitVec 64)
    (d : EpochDirectionPB) : SepProp :=
  tlb_vecU8ZeroCapAt A a d.next ∗
  tlb_vecU8ZeroCapAt A (a + 0x18#64) d.prev ∗
  ((a + 0x30#64) ↦₃₂ d.ctr) ∗
  memRegion (a + 0x34#64) 4

theorem tlb_epochDirectionZeroCapAt_entails_capOk (A : RustAlloc) (a : BitVec 64) (remLen : Nat)
    (d : EpochDirectionPB) :
    tlb_epochDirectionZeroCapAt A a d ⊢ epochDirectionPBCapOkAt A a remLen d :=
  sepConj_mono (tlb_vecU8ZeroCapAt_entails_vecU8CapOkAt A a remLen d.next)
    (sepConj_mono (tlb_vecU8ZeroCapAt_entails_vecU8CapOkAt A (a + 0x18#64) remLen d.prev)
      (Entails.refl _))

def tlb_ucEkSentCt1ReceivedZeroCapAt (A : RustAlloc) (a : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received) : SepProp :=
  tlb_vecU8ZeroCapAt A a u.dk ∗
  tlb_vecU8ZeroCapAt A (a + 0x18#64) u.ct1 ∗
  tlb_optAuthZeroCapAt A (a + 0x30#64) u.auth ∗
  ((a + 0x60#64) ↦₆₄ u.epoch)

theorem tlb_ucEkSentCt1ReceivedZeroCapAt_entails_cap (A : RustAlloc) (a : BitVec 64)
    (bsLen : Nat) (u : V1State.Unchunked.EkSentCt1Received) :
    tlb_ucEkSentCt1ReceivedZeroCapAt A a u ⊢
      unchunkedEkSentCt1ReceivedPBCapAt A a bsLen u :=
  sepConj_mono (tlb_vecU8ZeroCapAt_entails_cap A a bsLen u.dk)
    (sepConj_mono (tlb_vecU8ZeroCapAt_entails_cap A (a + 0x18#64) bsLen u.ct1)
      (sepConj_mono (tlb_optAuthZeroCapAt_entails_cap A (a + 0x30#64) bsLen u.auth)
        (Entails.refl _)))

def tlb_ucCt1SentZeroCapAt (A : RustAlloc) (a : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) : SepProp :=
  tlb_vecU8ZeroCapAt A a u.hdr ∗
  tlb_vecU8ZeroCapAt A (a + 0x18#64) u.es ∗
  tlb_vecU8ZeroCapAt A (a + 0x30#64) u.ct1 ∗
  tlb_optAuthZeroCapAt A (a + 0x48#64) u.auth ∗
  ((a + 0x78#64) ↦₆₄ u.epoch)

theorem tlb_ucCt1SentZeroCapAt_entails_cap (A : RustAlloc) (a : BitVec 64)
    (bsLen : Nat) (u : V1State.Unchunked.Ct1Sent) :
    tlb_ucCt1SentZeroCapAt A a u ⊢ unchunkedCt1SentPBCapAt A a bsLen u :=
  sepConj_mono (tlb_vecU8ZeroCapAt_entails_cap A a bsLen u.hdr)
    (sepConj_mono (tlb_vecU8ZeroCapAt_entails_cap A (a + 0x18#64) bsLen u.es)
      (sepConj_mono (tlb_vecU8ZeroCapAt_entails_cap A (a + 0x30#64) bsLen u.ct1)
        (sepConj_mono (tlb_optAuthZeroCapAt_entails_cap A (a + 0x48#64) bsLen u.auth)
          (Entails.refl _))))

noncomputable def tlb_authMergeTightSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop) :
    Spec (AuthMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap tlb_AuthDom
        (fun x => tlb_authenticatorZeroCapAt A.repAlloc x.msgPtr x.msg)
        (fun x => authenticatorPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp authMergeStack
  post := (authMergeSpecOfEnv A lim PreEnv PostEnv).post

noncomputable def tlb_polyDecoderMergeTightSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop) :
    Spec (PolyDecoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap tlb_PolyDecoderDom
        (fun x => tlb_polyDecoderZeroCapAt A.repAlloc x.msgPtr (polyDecoderToProto x.msg))
        (fun x => protoPolynomialDecoderAt A.repAlloc x.msgPtr (polyDecoderToProto x.msg)) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp polyMergeStack
  post := (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv).post

noncomputable def tlb_polyEncoderMergeTightSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop) :
    Spec (PolyEncoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      x.msg.polys.length + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap tlb_PolyEncoderDom
        (fun x => tlb_polyEncoderZeroCapAt A.repAlloc x.msgPtr (polyEncoderToProto x.msg))
        (fun x => protoPolynomialEncoderAt A.repAlloc x.msgPtr (polyEncoderToProto x.msg)) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp polyMergeStack
  post := (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv).post

noncomputable def tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedEkSentCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap tlb_UcEkSentCt1ReceivedDom
        (fun x => tlb_ucEkSentCt1ReceivedZeroCapAt A.repAlloc x.msgPtr x.msg)
        (fun x => unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedMergeStack
  post := (unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv).post

noncomputable def tlb_ucCt1SentMergeTightSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedCt1SentMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedCt1SentMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap tlb_UcCt1SentDom
        (fun x => tlb_ucCt1SentZeroCapAt A.repAlloc x.msgPtr x.msg)
        (fun x => unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedMergeStack
  post := (unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv).post

noncomputable def tlb_epochDirectionMergeTightSpecOfEnv {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop) :
    Spec (EpochDirectionMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap (tlb_EpochDirDom 79236)
        (fun x => tlb_epochDirectionZeroCapAt A.repAlloc x.msgPtr x.msg)
        (fun x => epochDirectionPBCapOkAt A.repAlloc x.msgPtr x.bs.length x.msg) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp epochDirectionMergeStack
  post := (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv).post

def tlb_AuthMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
    (lsmpl.base 295)
    (withLsCodeRoLoaded lsmpl
      (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf maxOps) (tlb_AuthGuardedEnvOf maxOps)))
abbrev tlb_AuthMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_AuthMergePlacedTightOkOf A lim 4 ext

/-- Placed tight subroutine contract for Block `296` (`PolynomialDecoder::merge`). -/
def tlb_PolyDecoderMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
    (lsmpl.base 296)
    (withLsCodeRoLoaded lsmpl
      (tlb_polyDecoderMergeTightSpecOfEnv A lim
        (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)))
abbrev tlb_PolyDecoderMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_PolyDecoderMergePlacedTightOkOf A lim 35 ext

/-- Placed tight subroutine contract for Block `297` (`PolynomialEncoder::merge`). -/
def tlb_PolyEncoderMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
    (lsmpl.base 297)
    (withLsCodeRoLoaded lsmpl
      (tlb_polyEncoderMergeTightSpecOfEnv A lim
        (tlb_PolyEncoderGuardedEnvOf maxOps) (tlb_PolyEncoderGuardedEnvOf maxOps)))
abbrev tlb_PolyEncoderMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_PolyEncoderMergePlacedTightOkOf A lim 35 ext

/-- Placed tight subroutine contract for Block `311` (`Unchunked.EkSentCt1Received::merge`). -/
def tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
    (lsmpl.base 311)
    (withLsCodeRoLoaded lsmpl
      (tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim
        (tlb_UcEkSentCt1ReceivedGuardedEnvOf maxOps) (tlb_UcEkSentCt1ReceivedGuardedEnvOf maxOps)))
abbrev tlb_UcEkSentCt1ReceivedMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim 8 ext

/-- Placed tight subroutine contract for Block `312` (`Unchunked.Ct1Sent::merge`). -/
def tlb_UcCt1SentMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
    (lsmpl.base 312)
    (withLsCodeRoLoaded lsmpl
      (tlb_ucCt1SentMergeTightSpecOfEnv A lim
        (tlb_UcCt1SentGuardedEnvOf maxOps) (tlb_UcCt1SentGuardedEnvOf maxOps)))
abbrev tlb_UcCt1SentMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_UcCt1SentMergePlacedTightOkOf A lim 10 ext

/-- Placed tight subroutine contract for Block `300` (`Chunked.Ct1Sampled::merge`). -/
def tlb_ChunkedCt1SampledMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 300 (Rust.withPanics ext))
    (lsmpl.base 300)
    (withLsCodeRoLoaded lsmpl
      (chunkedCt1SampledMergeSpecOfEnv A lim
        (tlb_ChunkedCt1SampledGuardedEnvOf maxOps) (tlb_ChunkedCt1SampledGuardedEnvOf maxOps)))
abbrev tlb_ChunkedCt1SampledMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedCt1SampledMergePlacedTightOkOf A lim 80 ext

/-- Placed tight subroutine contract for Block `301` (`Chunked.Ct2Sampled::merge`). -/
def tlb_ChunkedCt2SampledMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 301 (Rust.withPanics ext))
    (lsmpl.base 301)
    (withLsCodeRoLoaded lsmpl
      (chunkedCt2SampledMergeSpecOfEnv A lim
        (tlb_ChunkedCt2SampledGuardedEnvOf maxOps) (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)))
abbrev tlb_ChunkedCt2SampledMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim 39 ext

/-- Placed tight subroutine contract for Block `302` (`Chunked.HeaderSent::merge`). -/
def tlb_ChunkedHeaderSentMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext))
    (lsmpl.base 302)
    (withLsCodeRoLoaded lsmpl
      (chunkedHeaderSentMergeSpecOfEnv A lim
        (tlb_ChunkedHeaderSentGuardedEnvOf maxOps) (tlb_ChunkedHeaderSentGuardedEnvOf maxOps)))
abbrev tlb_ChunkedHeaderSentMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedHeaderSentMergePlacedTightOkOf A lim 76 ext

/-- Placed tight subroutine contract for Block `303` (`Chunked.Ct1Received::merge`). -/
def tlb_ChunkedCt1ReceivedMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext))
    (lsmpl.base 303)
    (withLsCodeRoLoaded lsmpl
      (chunkedCt1ReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedCt1ReceivedGuardedEnvOf maxOps) (tlb_ChunkedCt1ReceivedGuardedEnvOf maxOps)))
abbrev tlb_ChunkedCt1ReceivedMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedCt1ReceivedMergePlacedTightOkOf A lim 43 ext

/-- Placed tight subroutine contract for Block `304` (`Chunked.KeysSampled::merge`). -/
def tlb_ChunkedKeysSampledMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
    (lsmpl.base 304)
    (withLsCodeRoLoaded lsmpl
      (chunkedKeysSampledMergeSpecOfEnv A lim
        (tlb_ChunkedKeysSampledGuardedEnvOf maxOps) (tlb_ChunkedKeysSampledGuardedEnvOf maxOps)))
abbrev tlb_ChunkedKeysSampledMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedKeysSampledMergePlacedTightOkOf A lim 43 ext

/-- Placed tight subroutine contract for Block `305` (`Chunked.KeysUnsampled::merge`). -/
def tlb_ChunkedKeysUnsampledMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
    (lsmpl.base 305)
    (withLsCodeRoLoaded lsmpl
      (chunkedKeysUnsampledMergeSpecOfEnv A lim
        (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps) (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps)))
abbrev tlb_ChunkedKeysUnsampledMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedKeysUnsampledMergePlacedTightOkOf A lim 4 ext

/-- Placed tight subroutine contract for Block `306` (`Chunked.HeaderReceived::merge`). -/
def tlb_ChunkedHeaderReceivedMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
    (lsmpl.base 306)
    (withLsCodeRoLoaded lsmpl
      (chunkedHeaderReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps) (tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps)))
abbrev tlb_ChunkedHeaderReceivedMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedHeaderReceivedMergePlacedTightOkOf A lim 41 ext

/-- Placed tight subroutine contract for Block `307` (`Chunked.Ct1Acknowledged::merge`). -/
def tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
    (lsmpl.base 307)
    (withLsCodeRoLoaded lsmpl
      (chunkedCt1AcknowledgedMergeSpecOfEnv A lim
        (tlb_ChunkedCt1AcknowledgedGuardedEnvOf maxOps) (tlb_ChunkedCt1AcknowledgedGuardedEnvOf maxOps)))
abbrev tlb_ChunkedCt1AcknowledgedMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf A lim 45 ext

/-- Placed tight subroutine contract for Block `308` (`Chunked.NoHeaderReceived::merge`). -/
def tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 308 (Rust.withPanics ext))
    (lsmpl.base 308)
    (withLsCodeRoLoaded lsmpl
      (chunkedNoHeaderReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps) (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)))
abbrev tlb_ChunkedNoHeaderReceivedMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedNoHeaderReceivedMergePlacedTightOkOf A lim 39 ext

/-- Placed tight subroutine contract for Block `309` (`Chunked.EkSentCt1Received::merge`). -/
def tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 309 (Rust.withPanics ext))
    (lsmpl.base 309)
    (withLsCodeRoLoaded lsmpl
      (chunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps) (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps)))
abbrev tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf A lim 43 ext

/-- Placed tight subroutine contract for Block `310` (`Chunked.EkReceivedCt1Sampled::merge`). -/
def tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 310 (Rust.withPanics ext))
    (lsmpl.base 310)
    (withLsCodeRoLoaded lsmpl
      (chunkedEkReceivedCt1SampledMergeSpecOfEnv A lim
        (tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf maxOps)
        (tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf maxOps)))
abbrev tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf A lim 45 ext

/-- Placed tight subroutine contract for Block `298` (`V1State::merge`). -/
def tlb_V1StateMergePlacedTightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 298 (Rust.withPanics ext))
    (lsmpl.base 298)
    (withLsCodeRoLoaded lsmpl
      (v1StateMergePlacedSpecOfEnv A lim
        (tlb_V1StateMergeGuardedEnvOf maxOps) (tlb_V1StateMergeGuardedEnvOf maxOps)))
abbrev tlb_V1StateMergePlacedTightOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  tlb_V1StateMergePlacedTightOkOf A lim 80 ext

/-- Tight subroutine contract for Block `299` (`EpochDirectionPB::merge`) on the `blkPC_325` program.
-/
def tlb_EpochDirectionMergeBlk325TightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (sendOps recvOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 299)
    (withLsCodeRoLoaded lsmpl
      (tlb_epochDirectionMergeTightSpecOfEnv A lim
        (tlb_EpochDirectionGuardedEnvOf sendOps recvOps)
        (tlb_EpochDirectionGuardedEnvOf sendOps recvOps)))

/-- Tight subroutine contract for Block `298` (`V1State::merge`) on the `blkPC_325` program. -/
def tlb_V1StateMergeBlk325TightOkOf [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 298)
    (withLsCodeRoLoaded lsmpl
      (v1StateMergePlacedSpecOfEnv A lim
        (tlb_V1StateMergeGuardedEnvOf maxOps) (tlb_V1StateMergeGuardedEnvOf maxOps)))

/-! ## Block `325` (`spqr::decode_state`) Guarded-Tight Envelope and Inclusion Lemmas -/

theorem tlb_decodeStateTightEnv_nonFreeCount_le {maxOps : Nat} {evs : List AllocEvent}
    (h : tlb_DecodeStateTightEnvOf maxOps evs) :
    nonFreeCount evs ≤ maxOps :=
  h.1

theorem tlb_decodeStateTightEnv_nonFreeCount_le_128 {maxOps : Nat} (hle : maxOps ≤ 128)
    {evs : List AllocEvent} (h : tlb_DecodeStateTightEnvOf maxOps evs) :
    nonFreeCount evs ≤ 128 :=
  Nat.le_trans h.1 hle

theorem tlb_decodeState_phaseCreditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : SpqrTightHyps M) (maxOps : Nat) :
    PhaseCreditSpec M (tlb_DecodeStateTightEnvOf maxOps)
      decodeStateTightDeltaCum decodeStateTightDeltaLive
      decodeStateTightDeltaPeak decodeStateTightMaxReq :=
  spqrTightEvs_phaseCreditSpec hM hT maxOps 1307216 (Nat.le_refl 79236)

theorem tlb_decodeState_fine_phaseCreditSpec_tight (maxOps : Nat) :
    PhaseCreditSpec fineCostModel (tlb_DecodeStateTightEnvOf maxOps)
      decodeStateTightDeltaCum decodeStateTightDeltaLive
      decodeStateTightDeltaPeak decodeStateTightMaxReq :=
  spqrTightEvs_fine_phaseCreditSpec maxOps 1307216 (Nat.le_refl 79236)

/-- Input-state guard for `spqr::decode_state`: either empty (`[]`) or `TopStateTight F K x.st.bytes`.
-/
def tlb_DecodeStateDom (F : ShaCompress) (K : MlKem) (x : DecodeStateGhost) : Prop :=
  SpqrStateTight640 F K x.st.bytes

def tlb_DecodeStateGuardedEnvOf (F : ShaCompress) (K : MlKem) (maxOps : Nat) :
    DecodeStateGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv (tlb_DecodeStateDom F K) (tlb_DecodeStateTightEnvOf maxOps) DecodeStateEnv
abbrev tlb_DecodeStateGuardedEnv (F : ShaCompress) (K : MlKem) :
    DecodeStateGhost → List AllocEvent → Prop :=
  tlb_DecodeStateGuardedEnvOf F K 109

theorem tlb_decodeStateGuardedEnv_sub_tight_of_spqrStateTight640
    {F : ShaCompress} {K : MlKem} {maxOps : Nat} {x : DecodeStateGhost} {evs : List AllocEvent}
    (hGuard : SpqrStateTight640 F K x.st.bytes)
    (h : tlb_DecodeStateGuardedEnvOf F K maxOps x evs) :
    tlb_DecodeStateTightEnvOf maxOps evs :=
  tlb_guardedEnv_tight_of_dom (Dom := tlb_DecodeStateDom F K) hGuard h

theorem tlb_decodeStateGuardedEnv_sub_tight_of_topStateTight
    {F : ShaCompress} {K : MlKem} {maxOps : Nat} {x : DecodeStateGhost} {evs : List AllocEvent}
    (hTop : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight F K x.st.bytes)
    (h : tlb_DecodeStateGuardedEnvOf F K maxOps x evs) :
    tlb_DecodeStateTightEnvOf maxOps evs :=
  tlb_guardedEnv_tight_of_dom (Dom := tlb_DecodeStateDom F K) (Or.inr hTop) h

theorem tlb_decodeStateGuardedEnv_sub_tight_nil
    {F : ShaCompress} {K : MlKem} {maxOps : Nat} {x : DecodeStateGhost} {evs : List AllocEvent}
    (hNil : x.st.bytes = [])
    (h : tlb_DecodeStateGuardedEnvOf F K maxOps x evs) :
    tlb_DecodeStateTightEnvOf maxOps evs :=
  tlb_guardedEnv_tight_of_dom (Dom := tlb_DecodeStateDom F K) (Or.inl hNil) h

theorem tlb_decodeStateGuardedEnv_nonvacuous (F : ShaCompress) (K : MlKem)
    {maxOps : Nat} (hOps : 1 ≤ maxOps) :
    ∃ (bs : Bytes) (evs : List AllocEvent),
      evs ≠ [] ∧
      LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight F K bs ∧
      tlb_DecodeStateTightEnvOf maxOps evs := by
  refine ⟨spqrV1Init F K .a2b 0#256, [AllocEvent.alloc 32], by simp,
    topStateTight_spqrV1Init F K .a2b 0#256, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 + 1 ≤ maxOps
    omega
  · decide
  · intro _ _ _ hm
    simp at hm
  · intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    decide

theorem tlb_decodeStateGuardedEnv_mono {F : ShaCompress} {K : MlKem} {n₁ n₂ : Nat}
    (hle : n₁ ≤ n₂) {x : DecodeStateGhost} {evs : List AllocEvent}
    (h : tlb_DecodeStateGuardedEnvOf F K n₁ x evs) :
    tlb_DecodeStateGuardedEnvOf F K n₂ x evs := by
  rcases h with ⟨hd, ht⟩ | ⟨hnd, hf⟩
  · exact Or.inl ⟨hd, ht.mono hle (Nat.le_refl _) (Nat.le_refl _)⟩
  · exact Or.inr ⟨hnd, hf⟩

end LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
