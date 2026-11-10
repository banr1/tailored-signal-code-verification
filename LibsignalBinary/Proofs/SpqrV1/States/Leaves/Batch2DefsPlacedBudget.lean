/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget

/-!
# Exact `RustCliAllocBudget` Relocatable Specifications for SPQR V1 Receiver & Encoder Leaves

Exact binary `AllocEvent` envelopes (`*PreEnv`, `*PostEnv`, `*Env`) with non-vacuity witnesses,
two-envelope (`*SpecOfPrePostEnv`), single-envelope (`*SpecOfEnv`), and canonical (`*Spec` /
`*PlacedSpec`) `[LibsignalPlacement]` specifications under `RustCliAllocBudget M`, and `*PlacedOkX`
contract abbreviations for the receiver and encoder leaf transitions in `SpqrV1/States/Leaves`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPl_337 blkPl_338 blkPl_343 blkPl_346 blkPl_349
   blkPl_370 blkPl_382 lsProg_337 lsProg_338 lsProg_343 lsProg_346 lsProg_349
   lsProg_370 lsProg_382 lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (reserveCap withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Bytes MlKem SortedSetPt StatesResult spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt1AcknowledgedAt chunkedCt1ReceivedAt chunkedCt1ReceivedSize
   chunkedCt2SampledAt chunkedCt2SampledSize chunkedEkReceivedCt1SampledAt
   chunkedEkReceivedCt1SampledSize chunkedEkSentCt1ReceivedAt chunkedEkSentCt1ReceivedSize
   chunkedHeaderSentAt chunkedHeaderSentSize chunkedKeysSampledAt
   unchunkedCt1SentAt)
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1AcknowledgedRecvEkChunkGhost Ct1ReceivedRecvCt2ChunkGhost
   EkReceivedCt1SampledRecvCt1AckGhost HeaderSentRecvCt1ChunkGhost
   KeysSampledRecvCt1ChunkGhost PolyDecoderDecodedMessageGhost
   SendCt2EncoderGhost UnchunkedCt1SentRecvEkGhost UnchunkedSendCt2Ghost
   ct1AcknowledgedRecvEkChunkResAt ct1AcknowledgedRecvEkChunkStack
   ct1ReceivedRecvCt2ChunkStack ekReceivedCt1SampledRecvCt1AckStack
   headerSentRecvChunkAt headerSentRecvCt1ChunkStack keysSampledRecvCt1ChunkStack
   optVecU8At polyDecoderDecodedMessageStack sendCt2EncoderStack
   unchunkedCt1SentRecvEkResAt unchunkedRecvEkStack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep FreeOnlyEvs
   RustCliAllocBudget SeqEnv coarseCostModel rustAllocEvents rustReallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotsEnv addChunkSlotsEnv_nil)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv decodedMessageEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (SendCt2Reserve128Env UnchunkedCt1SentEkReceivedSendCt2PlacedOk
   UnchunkedSendCt2Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
   sendCt2ConcatHmacEvents sendCt2Seg23Events
   unchunkedCt1SentEkReceivedSendCt2PlacedSpec
   unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv
   unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (ctEqSliceROSpec)

attribute [local irreducible] addChunkTotal DecodedMessageEnv

/-- `VmPreserved`-strengthened read-only `ct_eq` contract re-exported from
    `TripleRatchet.Keys.DefsBudget` for `recv_ek` leaf proofs. -/
noncomputable abbrev ctEqSliceROBudgetSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  ctEqSliceROSpec

/-! ## 1. Callee Envelopes & Relocatable Budget Specifications (`Blocks 418, 347`) -/

/-- Exact allocation envelope of `<PolyDecoder as Decoder>::decoded_message` (`Block 418`). -/
def PolyDecoderDecodedMessageEnv (x : PolyDecoderDecodedMessageGhost)
    (evs : List AllocEvent) : Prop :=
  DecodedMessageEnv x.dec evs

abbrev PolyDecoderDecodedMessagePreEnv := PolyDecoderDecodedMessageEnv
abbrev PolyDecoderDecodedMessagePostEnv := PolyDecoderDecodedMessageEnv

theorem polyDecoderDecodedMessageEnv_nonempty (x : PolyDecoderDecodedMessageGhost) :
    ∃ evs, PolyDecoderDecodedMessageEnv x evs :=
  decodedMessageEnv_nonempty x.dec

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable specification of
    `<PolyDecoder as Decoder>::decoded_message` (`Block 418`). -/
def polyDecoderDecodedMessagePlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop) :
    Spec (PolyDecoderDecodedMessageGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec ∧
      spqrPolyApi.decoded_message x.dec = .ok x.outMsg ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA 24 ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp polyDecoderDecodedMessageStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      optVecU8At A.repAlloc x.outA x.outMsg ∗
      polyDecoderAt A.repAlloc x.decA x.dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp polyDecoderDecodedMessageStack

abbrev polyDecoderDecodedMessagePlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop) :
    Spec (PolyDecoderDecodedMessageGhost × M.σ) :=
  polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim Env Env

abbrev polyDecoderDecodedMessagePlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (PolyDecoderDecodedMessageGhost × M.σ) :=
  polyDecoderDecodedMessagePlacedSpecOfEnv M A lim PolyDecoderDecodedMessageEnv

/-- Non-emptiness of `UnchunkedSendCt2PreEnv` (`Block 347`, from `SendCt2PlacedBudget`). -/
theorem unchunkedSendCt2PreEnv_nonempty {F : ShaCompress} (x : UnchunkedSendCt2Ghost F) :
    ∃ evs, UnchunkedSendCt2PreEnv x evs :=
  ⟨sendCt2Seg23Events x.st.es ++ [] ++ sendCt2ConcatHmacEvents x.st.ct1.length,
    ⟨[], SendCt2Reserve128Env.nil x.st.ct1.length, rfl⟩⟩

/-- Non-emptiness of `UnchunkedSendCt2Env` (`Block 347`, from `SendCt2PlacedBudget`). -/
theorem unchunkedSendCt2Env_nonempty {F : ShaCompress} (x : UnchunkedSendCt2Ghost F) :
    ∃ evs, UnchunkedSendCt2Env x evs :=
  let ⟨evs, h⟩ := unchunkedSendCt2PreEnv_nonempty x
  ⟨evs, UnchunkedSendCt2PostEnv.of_pre h⟩

/-! ## 2. Target Envelopes & Specifications for Leaf Transitions -/

/-- Exact allocator event sequence for building `ct2 ++ mac` in
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`):
    `Vec::from_slice(ct2)` (`[]` if `ct2Len = 0`, else `rustAllocEvents ct2Len 1`) followed by
    `extend_from_slice(mac)` (`[]` if `macLen = 0`, `rustAllocEvents (reserveCap 0 0 macLen) 1`
    if `ct2Len = 0`, else `rustReallocEvents ct2Len (reserveCap ct2Len ct2Len macLen) 1`). -/
def sendCt2EncoderConcatEvents (ct2Len macLen : Nat) : List AllocEvent :=
  if ct2Len = 0 then
    if macLen = 0 then []
    else rustAllocEvents (reserveCap 0 0 macLen) 1
  else
    if macLen = 0 then rustAllocEvents ct2Len 1
    else rustAllocEvents ct2Len 1 ++
      rustReallocEvents ct2Len (reserveCap ct2Len ct2Len macLen) 1

/-- Allocation-phase prefix envelope of `send_ct2_encoder` (`Block 382`) parameterized by
    `(ct2Len, macLen)`: concatenation buffer allocation followed by `EncodeBytesEnv (ct2Len + macLen)`. -/
def SendCt2EncoderBytesPreEnv (ct2Len macLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv (· = sendCt2EncoderConcatEvents ct2Len macLen)
    (EncodeBytesEnv (ct2Len + macLen)) evs

/-- Full postcondition envelope of `send_ct2_encoder` (`Block 382`) parameterized by
    `(ct2Len, macLen)`: `SendCt2EncoderBytesPreEnv` followed by `FreeOnlyEvs` from dropping
    the temporary `ct2 ++ mac` buffer. -/
def SendCt2EncoderBytesPostEnv (ct2Len macLen : Nat) (evs : List AllocEvent) : Prop :=
  SeqEnv (SendCt2EncoderBytesPreEnv ct2Len macLen) FreeOnlyEvs evs

abbrev SendCt2EncoderBytesEnv := SendCt2EncoderBytesPostEnv

theorem sendCt2EncoderBytesPreEnv_nonempty (ct2Len macLen : Nat) :
    ∃ evs, SendCt2EncoderBytesPreEnv ct2Len macLen evs :=
  ⟨sendCt2EncoderConcatEvents ct2Len macLen ++ encodeBytesAllocEvents (ct2Len + macLen),
    SeqEnv.append rfl rfl⟩

theorem sendCt2EncoderBytesEnv_nonempty (ct2Len macLen : Nat) :
    ∃ evs, SendCt2EncoderBytesEnv ct2Len macLen evs :=
  let ⟨evs, h⟩ := sendCt2EncoderBytesPreEnv_nonempty ct2Len macLen
  ⟨evs, Or.inl h⟩

-- Non-vacuity check: `SendCt2EncoderBytesPreEnv 1088 32` fits in a 16 GiB `coarseCostModel` budget.
set_option synthInstance.maxSize 512 in
example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 0, physCap := 16 * 1024 * 1024 * 1024 }
      coarseCostModel.init
      (SendCt2EncoderBytesPreEnv 1088 32) := by
  have hc : sendCt2EncoderConcatEvents 1088 32 = [.alloc 1088, .realloc 1 1088 2176] := by decide
  have hall :
      sendCt2EncoderConcatEvents 1088 32 ++ encodeBytesAllocEvents (1088 + 32) =
        [.alloc 1088, .realloc 1 1088 2176,
         .alloc 1120, .alloc 1120, .alloc 1120, .alloc 1120,
         .alloc 1120, .alloc 1120, .alloc 1120, .alloc 1120,
         .alloc 1120, .alloc 1120, .alloc 1120, .alloc 1120,
         .alloc 1120, .alloc 1120, .alloc 1120, .alloc 1120] := by decide
  intro evs h
  unfold SendCt2EncoderBytesPreEnv SeqEnv EncodeBytesEnv at h
  rcases h with rfl | ⟨_, _, rfl, rfl, rfl⟩
  · rw [hc]
    dsimp only [FitsEvents, FitsEvent, FitsStep]
    decide
  · rw [hall]
    dsimp only [FitsEvents, FitsEvent, FitsStep]
    decide

/-- Allocation-phase prefix envelope of `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`). -/
def SendCt2EncoderPreEnv (x : SendCt2EncoderGhost) (evs : List AllocEvent) : Prop :=
  SendCt2EncoderBytesPreEnv x.ct2.length x.mac.length evs

/-- Postcondition envelope of `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`). -/
def SendCt2EncoderPostEnv (x : SendCt2EncoderGhost) (evs : List AllocEvent) : Prop :=
  SendCt2EncoderBytesPostEnv x.ct2.length x.mac.length evs

abbrev SendCt2EncoderEnv := SendCt2EncoderPostEnv

theorem sendCt2EncoderPreEnv_nonempty (x : SendCt2EncoderGhost) :
    ∃ evs, SendCt2EncoderPreEnv x evs :=
  sendCt2EncoderBytesPreEnv_nonempty x.ct2.length x.mac.length

theorem sendCt2EncoderEnv_nonempty (x : SendCt2EncoderGhost) :
    ∃ evs, SendCt2EncoderEnv x evs :=
  sendCt2EncoderBytesEnv_nonempty x.ct2.length x.mac.length

/-- Two-envelope (`PreEnv` / `PostEnv`) budget specification of
    `spqr::v1::chunked::send_ct::send_ct2_encoder` (`Block 382`). -/
def sendCt2EncoderSpecOfPrePostEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop) :
    Spec (SendCt2EncoderGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.ct2Ptr ∧ s.readReg64 .x2 = BitVec.ofNat 64 x.ct2.length ∧
      s.readReg64 .x3 = x.macPtr ∧ s.readReg64 .x4 = BitVec.ofNat 64 x.mac.length ∧
      x.ct2Ptr ≠ 0#64 ∧ x.macPtr ≠ 0#64 ∧
      CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi x.ct2 x.mac =
        .ok x.outEnc ∧
      FitsEnv M lim st (PreEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA 400 ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool lim st s ∗ stackAt s.sp sendCt2EncoderStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      polyEncoderAt A.repAlloc x.outA x.outEnc ∗
      (x.ct2Ptr ↦ₛ x.ct2) ∗
      (x.macPtr ↦ₛ x.mac) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp sendCt2EncoderStack

abbrev sendCt2EncoderSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Env : SendCt2EncoderGhost → List AllocEvent → Prop) :
    Spec (SendCt2EncoderGhost × M.σ) :=
  sendCt2EncoderSpecOfPrePostEnv M A lim Env Env

abbrev sendCt2EncoderSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (SendCt2EncoderGhost × M.σ) :=
  sendCt2EncoderSpecOfPrePostEnv M A lim SendCt2EncoderPreEnv SendCt2EncoderPostEnv

/-- Allocation-phase prefix envelope of `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek`
    (`Block 338`): `[]` (`recv_ek` never allocates). -/
def UnchunkedCt1SentRecvEkPreEnv {F : ShaCompress} (_x : UnchunkedCt1SentRecvEkGhost F)
    (evs : List AllocEvent) : Prop :=
  evs = []

/-- Postcondition envelope of `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (`Block 338`):
    `FreeOnlyEvs` (`recv_ek` deallocates `st.hdr` on `.ok` and consumed `Vec<u8>` buffers on `.error`). -/
def UnchunkedCt1SentRecvEkPostEnv {F : ShaCompress} (_x : UnchunkedCt1SentRecvEkGhost F)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs

abbrev UnchunkedCt1SentRecvEkEnv {F : ShaCompress} := @UnchunkedCt1SentRecvEkPostEnv F

theorem unchunkedCt1SentRecvEkPreEnv_nonempty {F : ShaCompress}
    (x : UnchunkedCt1SentRecvEkGhost F) :
    ∃ evs, UnchunkedCt1SentRecvEkPreEnv x evs :=
  ⟨[], rfl⟩

theorem unchunkedCt1SentRecvEkEnv_nonempty {F : ShaCompress}
    (x : UnchunkedCt1SentRecvEkGhost F) :
    ∃ evs, UnchunkedCt1SentRecvEkEnv x evs :=
  ⟨[], FreeOnlyEvs.nil⟩

/-- Two-envelope (`PreEnv` / `PostEnv`) budget specification of
    `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`Block 338`). -/
def unchunkedCt1SentRecvEkSpecOfPrePostEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop) :
    Spec (UnchunkedCt1SentRecvEkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.epoch ∧
      s.readReg64 .x3 = x.ekA ∧
      x.st.recv_ek K x.st.epoch x.ek = StatesResult.ofError x.res ∧
      FitsEnv M lim st (PreEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA 128 ∗
      unchunkedCt1SentAt A.repAlloc x.stA x.st ∗
      vecU8 A.repAlloc x.ekA x.ek ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedRecvEkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      unchunkedCt1SentRecvEkResAt A.repAlloc x.outA x.res ∗
      memRegion x.stA 128 ∗
      memRegion x.ekA 24 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp unchunkedRecvEkStack

abbrev unchunkedCt1SentRecvEkSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (K : MlKem)
    (Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop) :
    Spec (UnchunkedCt1SentRecvEkGhost F × M.σ) :=
  unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K Env Env

abbrev unchunkedCt1SentRecvEkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) (K : MlKem) :
    Spec (UnchunkedCt1SentRecvEkGhost F × M.σ) :=
  unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K
    UnchunkedCt1SentRecvEkPreEnv UnchunkedCt1SentRecvEkPostEnv

/-- Exact allocation-phase prefix envelope of `<EkReceivedCt1Sampled>::recv_ct1_ack` (`Block 343`):
    sequences `Unchunked::Ct1SentEkReceived::send_ct2` (`UnchunkedSendCt2Env`) with
    `SendCt2EncoderBytesPreEnv ct2.length mac.length` on `.ok (outUc, ct2, mac)`. -/
def EkReceivedCt1SampledRecvCt1AckPreEnv {F : ShaCompress} (K : MlKem)
    (x : EkReceivedCt1SampledRecvCt1AckGhost F) (evs : List AllocEvent) : Prop :=
  match x.st.uc.send_ct2 K with
  | .error _ => evs = []
  | .ok (outUc, ct2, mac) =>
    SeqEnv
      (UnchunkedSendCt2Env ⟨0#64, 0#64, x.st.uc, outUc, ct2, mac⟩)
      (SendCt2EncoderBytesPreEnv ct2.length mac.length)
      evs

/-- Postcondition envelope of `<EkReceivedCt1Sampled>::recv_ct1_ack` (`Block 343`):
    `EkReceivedCt1SampledRecvCt1AckPreEnv K x` followed by `FreeOnlyEvs` from epilogue drops of
    `ct2`, `mac`, and `sending_ct1`. -/
def EkReceivedCt1SampledRecvCt1AckPostEnv {F : ShaCompress} (K : MlKem)
    (x : EkReceivedCt1SampledRecvCt1AckGhost F) (evs : List AllocEvent) : Prop :=
  SeqEnv (EkReceivedCt1SampledRecvCt1AckPreEnv K x) FreeOnlyEvs evs

abbrev EkReceivedCt1SampledRecvCt1AckEnv {F : ShaCompress} (K : MlKem) :=
  @EkReceivedCt1SampledRecvCt1AckPostEnv F K

theorem ekReceivedCt1SampledRecvCt1AckPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : EkReceivedCt1SampledRecvCt1AckGhost F) :
    ∃ evs, EkReceivedCt1SampledRecvCt1AckPreEnv K x evs := by
  unfold EkReceivedCt1SampledRecvCt1AckPreEnv
  cases hsc : x.st.uc.send_ct2 K with
  | error _ => exact ⟨[], rfl⟩
  | ok val =>
    rcases val with ⟨outUc, ct2, mac⟩
    obtain ⟨e1, h1⟩ := unchunkedSendCt2Env_nonempty ⟨0#64, 0#64, x.st.uc, outUc, ct2, mac⟩
    obtain ⟨e2, h2⟩ := sendCt2EncoderBytesPreEnv_nonempty ct2.length mac.length
    exact ⟨e1 ++ e2, SeqEnv.append h1 h2⟩

theorem ekReceivedCt1SampledRecvCt1AckEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : EkReceivedCt1SampledRecvCt1AckGhost F) :
    ∃ evs, EkReceivedCt1SampledRecvCt1AckEnv K x evs :=
  let ⟨evs, h⟩ := ekReceivedCt1SampledRecvCt1AckPreEnv_nonempty K x
  ⟨evs, Or.inl h⟩

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable specification of
    `<EkReceivedCt1Sampled>::recv_ct1_ack` (`Block 343`). -/
def ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop) :
    Spec (EkReceivedCt1SampledRecvCt1AckGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      x.st.recv_ct1_ack K x.st.uc.epoch = .ok x.outSt ∧
      FitsEnv M lim st (PreEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA chunkedCt2SampledSize ∗
      chunkedEkReceivedCt1SampledAt A.repAlloc x.stA x.st ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim st s ∗ stackAt s.sp ekReceivedCt1SampledRecvCt1AckStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      chunkedCt2SampledAt A.repAlloc x.outA x.outSt ∗
      memRegion x.stA chunkedEkReceivedCt1SampledSize ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ekReceivedCt1SampledRecvCt1AckStack

abbrev ekReceivedCt1SampledRecvCt1AckPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop) :
    Spec (EkReceivedCt1SampledRecvCt1AckGhost F × M.σ) :=
  ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv M A lim F K Env Env

abbrev ekReceivedCt1SampledRecvCt1AckPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) :
    Spec (EkReceivedCt1SampledRecvCt1AckGhost F × M.σ) :=
  ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv M A lim F K
    (EkReceivedCt1SampledRecvCt1AckPreEnv K) (EkReceivedCt1SampledRecvCt1AckPostEnv K)

/-- Allocation-phase prefix envelope of `<Ct1Received>::recv_ct2_chunk` (`Block 346`):
    initializes a fresh `PolyDecoder` (`16` empty slots) and calls `add_chunk`. -/
def Ct1ReceivedRecvCt2ChunkPreEnv {F : ShaCompress} (_x : Ct1ReceivedRecvCt2ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs

/-- Postcondition envelope of `<Ct1Received>::recv_ct2_chunk` (`Block 346`):
    `Ct1ReceivedRecvCt2ChunkPreEnv` followed by `FreeOnlyEvs`. -/
def Ct1ReceivedRecvCt2ChunkPostEnv {F : ShaCompress} (x : Ct1ReceivedRecvCt2ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (Ct1ReceivedRecvCt2ChunkPreEnv x) FreeOnlyEvs evs

abbrev Ct1ReceivedRecvCt2ChunkEnv {F : ShaCompress} := @Ct1ReceivedRecvCt2ChunkPostEnv F

theorem ct1ReceivedRecvCt2ChunkPreEnv_nonempty {F : ShaCompress}
    (x : Ct1ReceivedRecvCt2ChunkGhost F) :
    ∃ evs, Ct1ReceivedRecvCt2ChunkPreEnv x evs :=
  ⟨[], addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new)⟩

theorem ct1ReceivedRecvCt2ChunkEnv_nonempty {F : ShaCompress}
    (x : Ct1ReceivedRecvCt2ChunkGhost F) :
    ∃ evs, Ct1ReceivedRecvCt2ChunkEnv x evs :=
  let ⟨evs, h⟩ := ct1ReceivedRecvCt2ChunkPreEnv_nonempty x
  ⟨evs, Or.inl h⟩

/-- Two-envelope (`PreEnv` / `PostEnv`) budget specification of
    `<Ct1Received>::recv_ct2_chunk` (`Block 346`). -/
def ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1ReceivedRecvCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      x.st.recv_ct2_chunk x.st.uc.epoch x.chunk = .ok x.outSt ∧
      FitsEnv M lim st (PreEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      chunkedCt1ReceivedAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp ct1ReceivedRecvCt2ChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      chunkedEkSentCt1ReceivedAt A.repAlloc x.outA x.outSt ∗
      memRegion x.stA chunkedCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ct1ReceivedRecvCt2ChunkStack

abbrev ct1ReceivedRecvCt2ChunkSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (Env : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1ReceivedRecvCt2ChunkGhost F × M.σ) :=
  ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F Env Env

abbrev ct1ReceivedRecvCt2ChunkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct1ReceivedRecvCt2ChunkGhost F × M.σ) :=
  ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F
    Ct1ReceivedRecvCt2ChunkPreEnv Ct1ReceivedRecvCt2ChunkPostEnv

/-- Allocation-phase prefix envelope of `<HeaderSent>::recv_ct1_chunk` (`Block 337`):
    `add_chunk` on `x.st.receiving_ct1` followed by `decoded_message`. -/
def HeaderSentRecvCt1ChunkPreEnv {F : ShaCompress} (x : HeaderSentRecvCt1ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (AddChunkSlotsEnv x.st.receiving_ct1.pts)
    (DecodedMessageEnv (addChunkTotal x.st.receiving_ct1 x.chunk)) evs

/-- Postcondition envelope of `<HeaderSent>::recv_ct1_chunk` (`Block 337`):
    `HeaderSentRecvCt1ChunkPreEnv` followed by `FreeOnlyEvs` from epilogue drops. -/
def HeaderSentRecvCt1ChunkPostEnv {F : ShaCompress} (x : HeaderSentRecvCt1ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (HeaderSentRecvCt1ChunkPreEnv x) FreeOnlyEvs evs

abbrev HeaderSentRecvCt1ChunkEnv {F : ShaCompress} := @HeaderSentRecvCt1ChunkPostEnv F

theorem headerSentRecvCt1ChunkPreEnv_nonempty {F : ShaCompress}
    (x : HeaderSentRecvCt1ChunkGhost F) :
    ∃ evs, HeaderSentRecvCt1ChunkPreEnv x evs := by
  obtain ⟨evs, hevs⟩ := decodedMessageEnv_nonempty (addChunkTotal x.st.receiving_ct1 x.chunk)
  exact ⟨evs, Or.inr ⟨[], evs, rfl, addChunkSlotsEnv_nil x.st.receiving_ct1.pts, hevs⟩⟩

theorem headerSentRecvCt1ChunkEnv_nonempty {F : ShaCompress}
    (x : HeaderSentRecvCt1ChunkGhost F) :
    ∃ evs, HeaderSentRecvCt1ChunkEnv x evs :=
  let ⟨evs, h⟩ := headerSentRecvCt1ChunkPreEnv_nonempty x
  ⟨evs, Or.inl h⟩

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable specification of
    `<HeaderSent>::recv_ct1_chunk` (`Block 337`). -/
def headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (HeaderSentRecvCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ct1 ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outRes ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedHeaderSentAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp headerSentRecvCt1ChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      headerSentRecvChunkAt A.repAlloc x.outA x.outRes ∗
      memRegion x.stA chunkedHeaderSentSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp headerSentRecvCt1ChunkStack

abbrev headerSentRecvCt1ChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (Env : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (HeaderSentRecvCt1ChunkGhost F × M.σ) :=
  headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F Env Env

abbrev headerSentRecvCt1ChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress) :
    Spec (HeaderSentRecvCt1ChunkGhost F × M.σ) :=
  headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F
    HeaderSentRecvCt1ChunkPreEnv HeaderSentRecvCt1ChunkPostEnv

/-- Exact allocation-phase prefix envelope of `<KeysSampled>::recv_ct1_chunk` (`Block 370`):
    initializes a fresh `PolyDecoder` (`16` empty slots), calls `add_chunk`, and calls
    `encode_bytes` on `x.st.uc.ek` (`EncodeBytesEnv x.st.uc.ek.length`). -/
def KeysSampledRecvCt1ChunkPreEnv {F : ShaCompress} (x : KeysSampledRecvCt1ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new))
    (EncodeBytesEnv x.st.uc.ek.length) evs

/-- Postcondition envelope of `<KeysSampled>::recv_ct1_chunk` (`Block 370`):
    `KeysSampledRecvCt1ChunkPreEnv` followed by `FreeOnlyEvs` from epilogue drops. -/
def KeysSampledRecvCt1ChunkPostEnv {F : ShaCompress} (x : KeysSampledRecvCt1ChunkGhost F)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (KeysSampledRecvCt1ChunkPreEnv x) FreeOnlyEvs evs

abbrev KeysSampledRecvCt1ChunkEnv {F : ShaCompress} := @KeysSampledRecvCt1ChunkPostEnv F

theorem keysSampledRecvCt1ChunkPreEnv_nonempty {F : ShaCompress}
    (x : KeysSampledRecvCt1ChunkGhost F) :
    ∃ evs, KeysSampledRecvCt1ChunkPreEnv x evs :=
  ⟨encodeBytesAllocEvents x.st.uc.ek.length,
    Or.inr ⟨[], _, rfl, addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new), rfl⟩⟩

theorem keysSampledRecvCt1ChunkEnv_nonempty {F : ShaCompress}
    (x : KeysSampledRecvCt1ChunkGhost F) :
    ∃ evs, KeysSampledRecvCt1ChunkEnv x evs :=
  let ⟨evs, h⟩ := keysSampledRecvCt1ChunkPreEnv_nonempty x
  ⟨evs, Or.inl h⟩

/-- Two-envelope (`PreEnv` / `PostEnv`) budget specification of
    `<KeysSampled>::recv_ct1_chunk` (`Block 370`). -/
def keysSampledRecvCt1ChunkSpecOfPrePostEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outSt ∧
      FitsEnv M lim st (PreEnv x) ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedKeysSampledAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp keysSampledRecvCt1ChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      chunkedHeaderSentAt A.repAlloc x.outA x.outSt ∗
      memRegion x.stA 504 ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp keysSampledRecvCt1ChunkStack

abbrev keysSampledRecvCt1ChunkSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) :=
  keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F Env Env

abbrev keysSampledRecvCt1ChunkSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) :=
  keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F
    KeysSampledRecvCt1ChunkPreEnv KeysSampledRecvCt1ChunkPostEnv

/-- Unplaced base two-envelope (`PreEnv` / `PostEnv`) budget specification of
    `<KeysSampled>::recv_ct1_chunk` (`Block 370`). -/
def keysSampledRecvCt1ChunkSpecOfPrePostEnvBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      x.st.recv_ct1_chunk x.st.uc.epoch x.chunk = .ok x.outSt ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA chunkedHeaderSentSize ∗
      chunkedKeysSampledAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim st s ∗ stackAt s.sp keysSampledRecvCt1ChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      chunkedHeaderSentAt A.repAlloc x.outA x.outSt ∗
      memRegion x.stA 504 ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp keysSampledRecvCt1ChunkStack

/-- Unplaced base single-envelope (`Env`) budget specification of
    `<KeysSampled>::recv_ct1_chunk` (`Block 370`). -/
abbrev keysSampledRecvCt1ChunkSpecOfEnvBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) :=
  keysSampledRecvCt1ChunkSpecOfPrePostEnvBase M A lim F Env Env

/-- Unplaced base canonical budget specification of `<KeysSampled>::recv_ct1_chunk` (`Block 370`). -/
abbrev keysSampledRecvCt1ChunkSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (KeysSampledRecvCt1ChunkGhost F × M.σ) :=
  keysSampledRecvCt1ChunkSpecOfPrePostEnvBase M A lim F
    KeysSampledRecvCt1ChunkPreEnv KeysSampledRecvCt1ChunkPostEnv

/-- Post-`decoded_message` allocation-phase prefix envelope of
    `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`):
    - `none` (`.stillReceiving`): `[]`;
    - `some ekBytes`: calls `Unchunked::Ct1Sent::recv_ek` (`FreeOnlyEvs`), returning `[]` (trailing
      deallocs absorbed in `PostEnv`) on `.error _`, or calling `Unchunked::send_ct2`
      (`UnchunkedSendCt2Env`) + `send_ct2_encoder` (`SendCt2EncoderBytesPreEnv`) on `.ok uc1`. -/
def Ct1AckRecvEkTailPreEnv {F : ShaCompress} (K : MlKem)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    Option Bytes → List AllocEvent → Prop
  | none, evs => evs = []
  | some ekBytes, evs =>
    match uc.recv_ek K uc.epoch ekBytes with
    | .error _ => evs = []
    | .ok uc1 =>
      SeqEnv FreeOnlyEvs
        (match uc1.send_ct2 K with
         | .error _ => (· = [])
         | .ok (outUc, ct2, mac) =>
           SeqEnv
             (UnchunkedSendCt2Env ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩)
             (SendCt2EncoderBytesPreEnv ct2.length mac.length))
        evs

theorem ct1AckRecvEkTailPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (optEk : Option Bytes) :
    ∃ evs, Ct1AckRecvEkTailPreEnv K uc optEk evs := by
  cases optEk with
  | none => exact ⟨[], rfl⟩
  | some ekBytes =>
    dsimp only [Ct1AckRecvEkTailPreEnv]
    cases hrek : uc.recv_ek K uc.epoch ekBytes with
    | error _ => exact ⟨[], rfl⟩
    | ok uc1 =>
      cases hsc : uc1.send_ct2 K with
      | error _ => exact ⟨[], Or.inl FreeOnlyEvs.nil⟩
      | ok val =>
        rcases val with ⟨outUc, ct2, mac⟩
        simp only [hsc]
        obtain ⟨e1, h1⟩ := unchunkedSendCt2Env_nonempty ⟨0#64, 0#64, uc1, outUc, ct2, mac⟩
        obtain ⟨e2, h2⟩ := sendCt2EncoderBytesPreEnv_nonempty ct2.length mac.length
        exact ⟨e1 ++ e2, Or.inr ⟨[], e1 ++ e2, rfl, FreeOnlyEvs.nil, SeqEnv.append h1 h2⟩⟩

/-- Exact allocation-phase prefix envelope of `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`):
    `add_chunk` on `x.st.receiving_ek`, followed by `decoded_message`, followed by
    `Ct1AckRecvEkTailPreEnv`. -/
def Ct1AcknowledgedRecvEkChunkPreEnv {F : ShaCompress} (K : MlKem)
    (x : Ct1AcknowledgedRecvEkChunkGhost F) (evs : List AllocEvent) : Prop :=
  let dec1 := addChunkTotal x.st.receiving_ek x.chunk
  SeqEnv (AddChunkSlotsEnv x.st.receiving_ek.pts)
    (SeqEnv (DecodedMessageEnv dec1)
      (Ct1AckRecvEkTailPreEnv K x.st.uc (decodedMessageTotal dec1)))
    evs

/-- Postcondition envelope of `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`):
    `Ct1AcknowledgedRecvEkChunkPreEnv K x` followed by `FreeOnlyEvs` from epilogue drops. -/
def Ct1AcknowledgedRecvEkChunkPostEnv {F : ShaCompress} (K : MlKem)
    (x : Ct1AcknowledgedRecvEkChunkGhost F) (evs : List AllocEvent) : Prop :=
  SeqEnv (Ct1AcknowledgedRecvEkChunkPreEnv K x) FreeOnlyEvs evs

abbrev Ct1AcknowledgedRecvEkChunkEnv {F : ShaCompress} (K : MlKem) :=
  @Ct1AcknowledgedRecvEkChunkPostEnv F K

theorem ct1AcknowledgedRecvEkChunkPreEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : Ct1AcknowledgedRecvEkChunkGhost F) :
    ∃ evs, Ct1AcknowledgedRecvEkChunkPreEnv K x evs := by
  unfold Ct1AcknowledgedRecvEkChunkPreEnv
  dsimp only
  generalize addChunkTotal x.st.receiving_ek x.chunk = dec1
  generalize decodedMessageTotal dec1 = optEk
  obtain ⟨eDec, heDec⟩ := decodedMessageEnv_nonempty dec1
  obtain ⟨eTail, heTail⟩ := ct1AckRecvEkTailPreEnv_nonempty K x.st.uc optEk
  exact ⟨[] ++ (eDec ++ eTail),
    Or.inr ⟨[], eDec ++ eTail, rfl, addChunkSlotsEnv_nil x.st.receiving_ek.pts,
      Or.inr ⟨eDec, eTail, rfl, heDec, heTail⟩⟩⟩

theorem ct1AcknowledgedRecvEkChunkEnv_nonempty {F : ShaCompress} (K : MlKem)
    (x : Ct1AcknowledgedRecvEkChunkGhost F) :
    ∃ evs, Ct1AcknowledgedRecvEkChunkEnv K x evs :=
  let ⟨evs, h⟩ := ct1AcknowledgedRecvEkChunkPreEnv_nonempty K x
  ⟨evs, Or.inl h⟩

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable specification of
    `<Ct1Acknowledged>::recv_ek_chunk` (`Block 349`). -/
def ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1AcknowledgedRecvEkChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.stA ∧
      s.readReg64 .x2 = x.st.uc.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.st.receiving_ek ∧
      x.st.recv_ek_chunk K x.st.uc.epoch x.chunk = StatesResult.ofError x.res ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA 528 ∗
      chunkedCt1AcknowledgedAt A.repAlloc x.stA x.st ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2PlacedRoAt ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp ct1AcknowledgedRecvEkChunkStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      ct1AcknowledgedRecvEkChunkResAt A.repAlloc x.outA x.res ∗
      memRegion x.stA 528 ∗
      chunkAt x.chunkA x.chunk ∗
      unchunkedSendCt2PlacedRoAt ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack

abbrev ct1AcknowledgedRecvEkChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop) :
    Spec (Ct1AcknowledgedRecvEkChunkGhost F × M.σ) :=
  ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K Env Env

abbrev ct1AcknowledgedRecvEkChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) :
    Spec (Ct1AcknowledgedRecvEkChunkGhost F × M.σ) :=
  ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K
    (Ct1AcknowledgedRecvEkChunkPreEnv K) (Ct1AcknowledgedRecvEkChunkPostEnv K)

/-! ## 3. Contract Abbreviations (`*PlacedOkX`) -/

def SendCt2EncoderPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : SendCt2EncoderGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_382 (Rust.withPanics ext)) (blkPl_382).base
    (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim PreEnv PostEnv))

abbrev SendCt2EncoderPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SendCt2EncoderGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  SendCt2EncoderPlacedOkXOfPrePostEnv M A lim Env Env ext

abbrev SendCt2EncoderPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  SendCt2EncoderPlacedOkXOfPrePostEnv M A lim SendCt2EncoderPreEnv SendCt2EncoderPostEnv ext

def UnchunkedCt1SentRecvEkPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
    (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K PreEnv PostEnv)

abbrev UnchunkedCt1SentRecvEkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  UnchunkedCt1SentRecvEkPlacedOkXOfPrePostEnv M A lim F K Env Env ext

abbrev UnchunkedCt1SentRecvEkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  UnchunkedCt1SentRecvEkPlacedOkXOfPrePostEnv M A lim F K
    UnchunkedCt1SentRecvEkPreEnv UnchunkedCt1SentRecvEkPostEnv ext

def EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_343 (Rust.withPanics ext)) (blkPl_343).base
    (withLsCodeLoaded lsmpl
      (ekReceivedCt1SampledRecvCt1AckPlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv))

abbrev EkReceivedCt1SampledRecvCt1AckPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : EkReceivedCt1SampledRecvCt1AckGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv M A lim F K Env Env ext

abbrev EkReceivedCt1SampledRecvCt1AckPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  EkReceivedCt1SampledRecvCt1AckPlacedOkXOfPrePostEnv M A lim F K
    (EkReceivedCt1SampledRecvCt1AckPreEnv K) (EkReceivedCt1SampledRecvCt1AckPostEnv K) ext

def Ct1ReceivedRecvCt2ChunkPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (PreEnv PostEnv : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_346 (Rust.withPanics ext)) (blkPl_346).base
    (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F PreEnv PostEnv))

abbrev Ct1ReceivedRecvCt2ChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (Env : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  Ct1ReceivedRecvCt2ChunkPlacedOkXOfPrePostEnv M A lim F Env Env ext

abbrev Ct1ReceivedRecvCt2ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  Ct1ReceivedRecvCt2ChunkPlacedOkXOfPrePostEnv M A lim F
    Ct1ReceivedRecvCt2ChunkPreEnv Ct1ReceivedRecvCt2ChunkPostEnv ext

def HeaderSentRecvCt1ChunkPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (PreEnv PostEnv : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_337 (Rust.withPanics ext)) (blkPl_337).base
    (withLsCodeRoLoaded lsmpl
      (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F PreEnv PostEnv))

abbrev HeaderSentRecvCt1ChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (Env : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  HeaderSentRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F Env Env ext

abbrev HeaderSentRecvCt1ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  HeaderSentRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F
    HeaderSentRecvCt1ChunkPreEnv HeaderSentRecvCt1ChunkPostEnv ext

def KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_370 (Rust.withPanics ext)) (blkPl_370).base
    (withLsCodeLoaded lsmpl
      (keysSampledRecvCt1ChunkSpecOfPrePostEnv M A lim F PreEnv PostEnv))

abbrev KeysSampledRecvCt1ChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F Env Env ext

abbrev KeysSampledRecvCt1ChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F
    KeysSampledRecvCt1ChunkPreEnv KeysSampledRecvCt1ChunkPostEnv ext

def Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_349 (Rust.withPanics ext)) (blkPl_349).base
    (withLsCodeRoLoaded lsmpl
      (ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv))

abbrev Ct1AcknowledgedRecvEkChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K Env Env ext

abbrev Ct1AcknowledgedRecvEkChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  Ct1AcknowledgedRecvEkChunkPlacedOkXOfPrePostEnv M A lim F K
    (Ct1AcknowledgedRecvEkChunkPreEnv K) (Ct1AcknowledgedRecvEkChunkPostEnv K) ext

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
