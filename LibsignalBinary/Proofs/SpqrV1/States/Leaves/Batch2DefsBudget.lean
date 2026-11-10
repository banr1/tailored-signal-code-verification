/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget

/-!
# Bounded `RustCliAllocBudget` Relocatable Specifications for SPQR V1 Receiver & Encoder Leaves

Bounded, non-vacuous `AllocEvent` envelopes (`*Env` and `*_nonempty`), envelope-parametric
(`*SpecOfEnv`) and default (`*Spec`) `[LibsignalPlacement]` specifications under
`RustCliAllocBudget M`, and `*PlacedOkX` contract abbreviations for `decoded_message`,
`<unchunked::Ct1SentEkReceived>::send_ct2`, `send_ct2_encoder`, `<unchunked::Ct1Sent>::recv_ek`,
`<EkReceivedCt1Sampled>::recv_ct1_ack`, `<Ct1Received>::recv_ct2_chunk`,
`<HeaderSent>::recv_ct1_chunk`, `<KeysSampled>::recv_ct1_chunk`, and
`<Ct1Acknowledged>::recv_ek_chunk`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPl_337 blkPl_338 blkPl_343 blkPl_346 blkPl_349 blkPl_370 blkPl_382
   lsProg_337 lsProg_338 lsProg_343 lsProg_346 lsProg_349 lsProg_370 lsProg_382
   lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap
  (vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (MlKem SortedSetPt StatesResult spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt1AcknowledgedAt chunkedCt1ReceivedAt chunkedCt1ReceivedSize
   chunkedCt2SampledAt chunkedCt2SampledSize chunkedEkReceivedCt1SampledAt
   chunkedEkReceivedCt1SampledSize chunkedEkSentCt1ReceivedAt chunkedEkSentCt1ReceivedSize
   chunkedHeaderSentAt chunkedHeaderSentSize chunkedKeysSampledAt
   unchunkedCt1SentAt unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt)
open CryptoVerification.SpqrV1.Unchunked
  (unchunkedSendCt2PlacedRoAt)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1AcknowledgedRecvEkChunkGhost Ct1ReceivedRecvCt2ChunkGhost
   EkReceivedCt1SampledRecvCt1AckGhost HeaderSentRecvCt1ChunkGhost
   KeysSampledRecvCt1ChunkGhost PolyDecoderDecodedMessageGhost
   SendCt2EncoderGhost UnchunkedCt1SentRecvEkGhost UnchunkedSendCt2Ghost
   ct1AcknowledgedRecvEkChunkResAt ct1AcknowledgedRecvEkChunkStack
   ct1ReceivedRecvCt2ChunkStack ekReceivedCt1SampledRecvCt1AckStack
   headerSentRecvChunkAt headerSentRecvCt1ChunkStack keysSampledRecvCt1ChunkStack
   optVecU8At polyDecoderDecodedMessageStack sendCt2EncoderStack
   unchunkedCt1SentRecvEkResAt unchunkedRecvEkStack unchunkedSendCt2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotsEnv addChunkSlotsEnv_nil)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv decodedMessageEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs)

attribute [local irreducible] addChunkTotal DecodedMessageEnv

/-! ## 1. Callee Envelopes & Relocatable Budget Specifications -/

/-- Allocation envelope of `<PolyDecoder as Decoder>::decoded_message` (`Block 418`). -/
def PolyDecoderDecodedMessageEnv (x : PolyDecoderDecodedMessageGhost)
    (evs : List AllocEvent) : Prop :=
  DecodedMessageEnv x.dec evs

theorem polyDecoderDecodedMessageEnv_nonempty (x : PolyDecoderDecodedMessageGhost) :
    ∃ evs, PolyDecoderDecodedMessageEnv x evs :=
  decodedMessageEnv_nonempty x.dec

/-- Envelope-parametric relocatable specification of `<PolyDecoder as Decoder>::decoded_message` (`Block 418`). -/
def polyDecoderDecodedMessagePlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop) :
    Spec (PolyDecoderDecodedMessageGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      spqrPolyApi.decoded_message x.dec = .ok x.outMsg ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA 24 ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp polyDecoderDecodedMessageStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      optVecU8At A.repAlloc x.outA x.outMsg ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp polyDecoderDecodedMessageStack

abbrev polyDecoderDecodedMessagePlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PolyDecoderDecodedMessageGhost × M.σ) :=
  polyDecoderDecodedMessagePlacedSpecOfEnv M A lim PolyDecoderDecodedMessageEnv

/-- Bounded allocation envelope of `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (`Block 347`). -/
def UnchunkedSendCt2Env {F : ShaCompress} (_x : UnchunkedSendCt2Ghost F)
    (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 16 8192 evs

theorem unchunkedSendCt2Env_nonempty {F : ShaCompress} (x : UnchunkedSendCt2Ghost F) :
    ∃ evs, UnchunkedSendCt2Env x evs :=
  ⟨[], SpqrBoundedEvs.nil 16 8192⟩

/-- Envelope-parametric relocatable specification of `<Unchunked.SendCt.Ct1SentEkReceived>::send_ct2` (`Block 347`). -/
def unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧
      x.st.send_ct2 K = .ok (x.outUc, x.ct2, x.mac) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA 104 ∗
      unchunkedCt1SentEkReceivedAt A.repAlloc x.stA x.st ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedSendCt2Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      unchunkedCt2SentAt A.repAlloc x.outA x.outUc ∗
      vecU8 A.repAlloc (x.outA + 56#64) x.ct2 ∗
      vecU8 A.repAlloc (x.outA + 80#64) x.mac ∗
      memRegion x.stA 128 ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp unchunkedSendCt2Stack

abbrev unchunkedCt1SentEkReceivedSendCt2PlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) :=
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv M A lim F K UnchunkedSendCt2Env

/-! ## 2. Target Specifications for Leaf Transitions -/

/-- Allocation envelope of `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`):
    concatenation buffer reserves (`≤ 4` allocations, request `≤ 2 * (ct2.length + mac.length) + 64`),
    followed by `EncodeBytesEnv (ct2.length + mac.length)`, followed by `FreeOnlyEvs`. -/
def SendCt2EncoderEnv (x : SendCt2EncoderGhost) (evs : List AllocEvent) : Prop :=
  SeqEnv (SpqrBoundedEvs 4 (2 * (x.ct2.length + x.mac.length) + 64))
    (SeqEnv (EncodeBytesEnv (x.ct2.length + x.mac.length)) FreeOnlyEvs) evs

theorem sendCt2EncoderEnv_nonempty (x : SendCt2EncoderGhost) :
    ∃ evs, SendCt2EncoderEnv x evs :=
  ⟨encodeBytesAllocEvents (x.ct2.length + x.mac.length),
    Or.inr ⟨[], _, rfl, SpqrBoundedEvs.nil _ _, Or.inl rfl⟩⟩

/-- Envelope-parametric budget specification of `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`). -/
def sendCt2EncoderSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SendCt2EncoderGhost → List AllocEvent → Prop) :
    Spec (SendCt2EncoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.ct2Ptr ∧ s.readReg64 .x2 = BitVec.ofNat 64 x.ct2.length ∧
      s.readReg64 .x3 = x.macPtr ∧ s.readReg64 .x4 = BitVec.ofNat 64 x.mac.length ∧
      x.ct2Ptr ≠ 0#64 ∧ x.macPtr ≠ 0#64 ∧
      CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi x.ct2 x.mac = .ok x.outEnc ∧
      FitsEnv M lim st (Env x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA 400 ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool lim st s ∗ stackAt s.sp sendCt2EncoderStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      polyEncoderAt A.repAlloc x.outA x.outEnc ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp sendCt2EncoderStack

abbrev sendCt2EncoderSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SendCt2EncoderGhost × M.σ) :=
  sendCt2EncoderSpecOfEnv M A lim SendCt2EncoderEnv

/-- Unplaced base envelope-parametric budget specification of
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`). -/
def sendCt2EncoderSpecOfEnvBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SendCt2EncoderGhost → List AllocEvent → Prop) :
    Spec (SendCt2EncoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.ct2Ptr ∧ s.readReg64 .x2 = BitVec.ofNat 64 x.ct2.length ∧
      s.readReg64 .x3 = x.macPtr ∧ s.readReg64 .x4 = BitVec.ofNat 64 x.mac.length ∧
      x.ct2Ptr ≠ 0#64 ∧ x.macPtr ≠ 0#64 ∧
      CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi x.ct2 x.mac = .ok x.outEnc ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA 400 ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool lim st s ∗ stackAt s.sp sendCt2EncoderStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      polyEncoderAt A.repAlloc x.outA x.outEnc ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp sendCt2EncoderStack

/-- Unplaced base default budget specification of
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`). -/
abbrev sendCt2EncoderSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SendCt2EncoderGhost × M.σ) :=
  sendCt2EncoderSpecOfEnvBase M A lim SendCt2EncoderEnv

/-- Allocation envelope of `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (`Block 338`):
    `FreeOnlyEvs` (`recv_ek` never allocates and only deallocates consumed `Vec<u8>` buffers on error). -/
def UnchunkedCt1SentRecvEkEnv {F : ShaCompress} (_x : UnchunkedCt1SentRecvEkGhost F)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs

theorem unchunkedCt1SentRecvEkEnv_nonempty {F : ShaCompress} (x : UnchunkedCt1SentRecvEkGhost F) :
    ∃ evs, UnchunkedCt1SentRecvEkEnv x evs :=
  ⟨[], FreeOnlyEvs.nil⟩

/-- Envelope-parametric budget specification of `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`Block 338`). -/
def unchunkedCt1SentRecvEkSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (K : MlKem)
    (Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop) :
    Spec (UnchunkedCt1SentRecvEkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.epoch ∧
      s.readReg64 .x3 = x.ekA ∧
      x.st.recv_ek K x.st.epoch x.ek = StatesResult.ofError x.res ∧
      FitsEnv M lim st (Env x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA 128 ∗
      unchunkedCt1SentAt A.repAlloc x.stA x.st ∗
      vecU8 A.repAlloc x.ekA x.ek ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedRecvEkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      unchunkedCt1SentRecvEkResAt A.repAlloc x.outA x.res ∗
      memRegion x.stA 128 ∗
      memRegion x.ekA 24 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp unchunkedRecvEkStack

abbrev unchunkedCt1SentRecvEkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (K : MlKem) :
    Spec (UnchunkedCt1SentRecvEkGhost F × M.σ) :=
  unchunkedCt1SentRecvEkSpecOfEnv M A lim F K UnchunkedCt1SentRecvEkEnv

/-- Bounded allocation envelope of `<EkReceivedCt1Sampled>::recv_ct1_ack` (`Block 343`):
    calls `Unchunked::send_ct2` + `send_ct2_encoder` (`ct2 = 1088`B, `mac = 32`B) + drops. -/
def EkReceivedCt1SampledRecvCt1AckEnv {F : ShaCompress} (_x : EkReceivedCt1SampledRecvCt1AckGhost F)
    (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 40 16384 evs

theorem ekReceivedCt1SampledRecvCt1AckEnv_nonempty {F : ShaCompress}
    (x : EkReceivedCt1SampledRecvCt1AckGhost F) :
    ∃ evs, EkReceivedCt1SampledRecvCt1AckEnv x evs :=
  ⟨[], SpqrBoundedEvs.nil 40 16384⟩

/-- Envelope-parametric relocatable specification of `<EkReceivedCt1Sampled>::recv_ct1_ack` (`Block 343`). -/
def ekReceivedCt1SampledRecvCt1AckPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop) :
    Spec (EkReceivedCt1SampledRecvCt1AckGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      x.st.recv_ct1_ack K x.st.uc.epoch = .ok x.outSt ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkedCt2SampledSize ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.stA x.st ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim st s ∗ stackAt s.sp ekReceivedCt1SampledRecvCt1AckStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedCt2SampledAt A.repAlloc x.outA x.outSt ∗
      memRegion x.stA chunkedEkReceivedCt1SampledSize ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ekReceivedCt1SampledRecvCt1AckStack

abbrev ekReceivedCt1SampledRecvCt1AckPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) :
    Spec (EkReceivedCt1SampledRecvCt1AckGhost F × M.σ) :=
  ekReceivedCt1SampledRecvCt1AckPlacedSpecOfEnv M A lim F K EkReceivedCt1SampledRecvCt1AckEnv

/-- Allocation envelope of `<Ct1Received>::recv_ct2_chunk` (`Block 346`):
    initializes a fresh `PolyDecoder` (`16` empty slots) and calls `add_chunk`. -/
def Ct1ReceivedRecvCt2ChunkEnv {F : ShaCompress} (_x : Ct1ReceivedRecvCt2ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs

theorem ct1ReceivedRecvCt2ChunkEnv_nonempty {F : ShaCompress}
    (x : Ct1ReceivedRecvCt2ChunkGhost F) :
    ∃ evs, Ct1ReceivedRecvCt2ChunkEnv x evs :=
  ⟨[], addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new)⟩

/-- Envelope-parametric budget specification of `<Ct1Received>::recv_ct2_chunk` (`Block 346`). -/
def ct1ReceivedRecvCt2ChunkSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1ReceivedRecvCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      x.st.recv_ct2_chunk x.st.uc.epoch x.chunk = .ok x.outSt ∧
      FitsEnv M lim st (Env x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      chunkedCt1ReceivedAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp ct1ReceivedRecvCt2ChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedEkSentCt1ReceivedAt A.repAlloc x.outA x.outSt ∗
      memRegion x.stA chunkedCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ct1ReceivedRecvCt2ChunkStack

abbrev ct1ReceivedRecvCt2ChunkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct1ReceivedRecvCt2ChunkGhost F × M.σ) :=
  ct1ReceivedRecvCt2ChunkSpecOfEnv M A lim F Ct1ReceivedRecvCt2ChunkEnv

/-- Allocation envelope of `<HeaderSent>::recv_ct1_chunk` (`Block 337`):
    `add_chunk` on `x.st.receiving_ct1`, followed by `decoded_message`, followed by `FreeOnlyEvs`. -/
def HeaderSentRecvCt1ChunkEnv {F : ShaCompress} (x : HeaderSentRecvCt1ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (AddChunkSlotsEnv x.st.receiving_ct1.pts)
    (SeqEnv (DecodedMessageEnv (addChunkTotal x.st.receiving_ct1 x.chunk)) FreeOnlyEvs) evs

theorem headerSentRecvCt1ChunkEnv_nonempty {F : ShaCompress}
    (x : HeaderSentRecvCt1ChunkGhost F) :
    ∃ evs, HeaderSentRecvCt1ChunkEnv x evs := by
  obtain ⟨evs, hevs⟩ := decodedMessageEnv_nonempty (addChunkTotal x.st.receiving_ct1 x.chunk)
  exact ⟨evs, Or.inr ⟨[], evs, rfl, addChunkSlotsEnv_nil x.st.receiving_ct1.pts, Or.inl hevs⟩⟩

/-- Envelope-parametric relocatable specification of `<HeaderSent>::recv_ct1_chunk` (`Block 337`). -/
def headerSentRecvCt1ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (HeaderSentRecvCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ct1 ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outRes ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedHeaderSentAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp headerSentRecvCt1ChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      headerSentRecvChunkAt A.repAlloc x.outA x.outRes ∗
      memRegion x.stA chunkedHeaderSentSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp headerSentRecvCt1ChunkStack

abbrev headerSentRecvCt1ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (HeaderSentRecvCt1ChunkGhost F × M.σ) :=
  headerSentRecvCt1ChunkPlacedSpecOfEnv M A lim F HeaderSentRecvCt1ChunkEnv

/-- Allocation envelope of `<KeysSampled>::recv_ct1_chunk` (`Block 370`):
    initializes a fresh `PolyDecoder` (`16` empty slots), calls `add_chunk` + `encode_bytes`
    on the `1184`B EK + `FreeOnlyEvs`. -/
def KeysSampledRecvCt1ChunkEnv {F : ShaCompress} (_x : KeysSampledRecvCt1ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SpqrBoundedEvs 36 8192 evs

theorem keysSampledRecvCt1ChunkEnv_nonempty {F : ShaCompress}
    (x : KeysSampledRecvCt1ChunkGhost F) :
    ∃ evs, KeysSampledRecvCt1ChunkEnv x evs :=
  ⟨[], SpqrBoundedEvs.nil 36 8192⟩

/-- Envelope-parametric budget specification of `<KeysSampled>::recv_ct1_chunk` (`Block 370`). -/
def keysSampledRecvCt1ChunkSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outSt ∧
      FitsEnv M lim st (Env x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedKeysSampledAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp keysSampledRecvCt1ChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      chunkedHeaderSentAt A.repAlloc x.outA x.outSt ∗
      memRegion x.stA 504 ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp keysSampledRecvCt1ChunkStack

abbrev keysSampledRecvCt1ChunkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) :=
  keysSampledRecvCt1ChunkSpecOfEnv M A lim F KeysSampledRecvCt1ChunkEnv

/-- Allocation envelope of `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`):
    `add_chunk` on `x.st.receiving_ek`, followed by `decoded_message`, followed by optional
    `Unchunked::recv_ek` + `Unchunked::send_ct2` + `send_ct2_encoder` (`≤ 40` allocations,
    request `≤ 16384`), followed by `FreeOnlyEvs`. -/
def Ct1AcknowledgedRecvEkChunkEnv {F : ShaCompress} (x : Ct1AcknowledgedRecvEkChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (AddChunkSlotsEnv x.st.receiving_ek.pts)
    (SeqEnv (DecodedMessageEnv (addChunkTotal x.st.receiving_ek x.chunk))
      (SeqEnv (SpqrBoundedEvs 40 16384) FreeOnlyEvs)) evs

theorem ct1AcknowledgedRecvEkChunkEnv_nonempty {F : ShaCompress}
    (x : Ct1AcknowledgedRecvEkChunkGhost F) :
    ∃ evs, Ct1AcknowledgedRecvEkChunkEnv x evs := by
  obtain ⟨evs, hevs⟩ := decodedMessageEnv_nonempty (addChunkTotal x.st.receiving_ek x.chunk)
  exact ⟨evs, Or.inr ⟨[], evs, rfl, addChunkSlotsEnv_nil x.st.receiving_ek.pts, Or.inl hevs⟩⟩

/-- Envelope-parametric relocatable specification of `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`). -/
def ct1AcknowledgedRecvEkChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1AcknowledgedRecvEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ek ∧
      x.st.recv_ek_chunk K x.st.uc.epoch x.chunk = StatesResult.ofError x.res ∧
      FitsEnv M lim st (Env x)⌝ ∗
      memRegion x.outA 528 ∗
      chunkedCt1AcknowledgedAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2PlacedRoAt ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp ct1AcknowledgedRecvEkChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env x evs⌝ ∗
      ct1AcknowledgedRecvEkChunkResAt A.repAlloc x.outA x.res ∗
      memRegion x.stA 528 ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2PlacedRoAt ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack

abbrev ct1AcknowledgedRecvEkChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) :
    Spec (Ct1AcknowledgedRecvEkChunkGhost F × M.σ) :=
  ct1AcknowledgedRecvEkChunkPlacedSpecOfEnv M A lim F K Ct1AcknowledgedRecvEkChunkEnv

/-! ## 3. Contract Abbreviations (`*PlacedOkX`) -/

def SendCt2EncoderPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_382 (Rust.withPanics ext)) (blkPl_382).base
    (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim))

def UnchunkedCt1SentRecvEkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
    (unchunkedCt1SentRecvEkSpec M A lim F K)

def EkReceivedCt1SampledRecvCt1AckPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_343 (Rust.withPanics ext)) (blkPl_343).base
    (withLsCodeLoaded lsmpl (ekReceivedCt1SampledRecvCt1AckPlacedSpec M A lim F K))

def Ct1ReceivedRecvCt2ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_346 (Rust.withPanics ext)) (blkPl_346).base
    (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec M A lim F))

def HeaderSentRecvCt1ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_337 (Rust.withPanics ext)) (blkPl_337).base
    (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec M A lim F))

def KeysSampledRecvCt1ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_370 (Rust.withPanics ext)) (blkPl_370).base
    (withLsCodeLoaded lsmpl (keysSampledRecvCt1ChunkSpec M A lim F))

def Ct1AcknowledgedRecvEkChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_349 (Rust.withPanics ext)) (blkPl_349).base
    (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec M A lim F K))

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsBudget
