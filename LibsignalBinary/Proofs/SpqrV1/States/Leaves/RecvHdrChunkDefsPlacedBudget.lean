/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public import LibsignalBinary.Heap.SpecBudget

/-!
# `<NoHeaderReceived>::recv_hdr_chunk`: Budget-Threaded Specifications (Block `369`)

Allocator-event envelopes (`NoHeaderReceivedRecvHdrChunkEnv`) and budget-threaded
`[LibsignalPlacement]` specifications (`noHeaderReceivedRecvHdrChunkPlacedSpec{,OfPrePostEnv,OfEnv}`)
and contracts (`NoHeaderReceivedRecvHdrChunkPlacedOkX{,OfEnv}`) for Block `369`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPl_369 lsProg_369 lsmpl)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Bytes)
open CryptoVerification.SpqrV1.Drop (chunkedNoHeaderReceivedAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkGhost chunkedHeaderReceivedSize
   chunkedNoHeaderReceivedSize noHeaderReceivedRecvChunkResultAt
   noHeaderReceivedRecvHdrChunkStackX)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotsEnv addChunkSlotsEnv_nil)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv decodedMessageEnv_nonempty)

/-! ## 1. Allocator Event Envelopes for `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) -/

/-- Heap allocation events for splitting `hdrFull` (`64 ≤ hdrFullLen`) into `mac` (`hdrFull.drop 64`)
    and `hdr` (`hdrFull.take 64`, 64 bytes). -/
def recvHdrChunkAllocMacHdrEvents (hdrFullLen : Nat) : List AllocEvent :=
  (if hdrFullLen = 64 then [] else rustAllocEvents (hdrFullLen - 64) 1) ++
    rustAllocEvents 64 1

/-- Heap allocation events for `slice_concat_3` (`33 + 8 + 64 = 105` bytes) followed by
    `libcrux_hmac::hmac` (`SHA256`) inside `Authenticator::verify_hdr`. -/
def recvHdrChunkHmacEvents : List AllocEvent :=
  rustAllocEvents 105 1 ++ libcruxHmacSha256Events

/-- Post-`decoded_message` allocation envelope of `<NoHeaderReceived>::recv_hdr_chunk`:
    - `none` (`.stillReceiving`): `[]`;
    - `some hdrFull` with `hdrFull.length < 64` (slice bounds panic before `mac`/`hdr` alloc): `[]`;
    - `some hdrFull` with `64 ≤ hdrFull.length`: `mac`/`hdr` slice allocations + `slice_concat_3` +
      `libcrux_hmac::hmac`, followed by `FreeOnlyEvs` from epilogue buffer drops. -/
def RecvHdrChunkTailEnv : Option Bytes → List AllocEvent → Prop
  | none, evs => evs = []
  | some hdrFull, evs =>
    if hdrFull.length < 64 then
      evs = []
    else
      SeqEnv
        (· = recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents)
        FreeOnlyEvs
        evs

theorem recvHdrChunkTailEnv_nonempty (optHdr : Option Bytes) :
    ∃ evs, RecvHdrChunkTailEnv optHdr evs := by
  cases optHdr with
  | none => exact ⟨[], rfl⟩
  | some hdrFull =>
    dsimp only [RecvHdrChunkTailEnv]
    split
    · exact ⟨[], rfl⟩
    · exact ⟨recvHdrChunkAllocMacHdrEvents hdrFull.length ++ recvHdrChunkHmacEvents, Or.inl rfl⟩

/-- Canonical allocator event envelope of `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`):
    - `x.epoch != x.self.uc.epoch` (immediate epoch-mismatch panic): `[]`;
    - `x.epoch == x.self.uc.epoch`: sequential composition of `<PolyDecoder>::add_chunk`
      (`AddChunkSlotsEnv`), `<PolyDecoder>::decoded_message` (`DecodedMessageEnv`), and
      `RecvHdrChunkTailEnv`. -/
def NoHeaderReceivedRecvHdrChunkEnv {F : ShaCompress}
    (x : NoHeaderReceivedRecvHdrChunkGhost F) (evs : List AllocEvent) : Prop :=
  if x.epoch != x.self.uc.epoch then
    evs = []
  else
    let receivingHdr := addChunkTotal x.self.receiving_hdr x.chunk
    SeqEnv (AddChunkSlotsEnv x.self.receiving_hdr.pts)
      (SeqEnv (DecodedMessageEnv receivingHdr)
        (RecvHdrChunkTailEnv (decodedMessageTotal receivingHdr)))
      evs

theorem noHeaderReceivedRecvHdrChunkEnv_nonempty {F : ShaCompress}
    (x : NoHeaderReceivedRecvHdrChunkGhost F) :
    ∃ evs, NoHeaderReceivedRecvHdrChunkEnv x evs := by
  unfold NoHeaderReceivedRecvHdrChunkEnv
  split
  · exact ⟨[], rfl⟩
  · dsimp only
    generalize addChunkTotal x.self.receiving_hdr x.chunk = receivingHdr
    generalize decodedMessageTotal receivingHdr = optHdr
    rcases decodedMessageEnv_nonempty receivingHdr with ⟨eDec, heDec⟩
    rcases recvHdrChunkTailEnv_nonempty optHdr with ⟨eTail, heTail⟩
    exact ⟨[] ++ (eDec ++ eTail),
      Or.inr ⟨[], eDec ++ eTail, rfl, addChunkSlotsEnv_nil x.self.receiving_hdr.pts,
        Or.inr ⟨eDec, eTail, rfl, heDec, heTail⟩⟩⟩

/-! ## 2. Budget-Threaded Relocatable Specifications & Contracts (Block `369`) -/

/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded relocatable specification of
    `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`). Retains the genuine model-level panic
    disjunct `(x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true` while eliminating
    `∨ allocFailedIn s0 sf`. -/
def noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop) :
    Spec (NoHeaderReceivedRecvHdrChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_hdr ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA chunkedHeaderReceivedSize ∗
      chunkedNoHeaderReceivedAt A.repAlloc x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗
      stackAt s.sp noHeaderReceivedRecvHdrChunkStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      noHeaderReceivedRecvChunkResultAt A.repAlloc x.outA
        (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
      memRegion x.selfA chunkedNoHeaderReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX
  onPanic := fun (x, _) s0 sf =>
    ⌜(x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Single-envelope (`Env`) budget-threaded relocatable specification of
    `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`). -/
abbrev noHeaderReceivedRecvHdrChunkPlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop) :
    Spec (NoHeaderReceivedRecvHdrChunkGhost F × M.σ) :=
  noHeaderReceivedRecvHdrChunkPlacedSpecOfPrePostEnv M A lim F Env Env

/-- Canonical budget-threaded relocatable specification of
    `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`). -/
abbrev noHeaderReceivedRecvHdrChunkPlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) :
    Spec (NoHeaderReceivedRecvHdrChunkGhost F × M.σ) :=
  noHeaderReceivedRecvHdrChunkPlacedSpecOfEnv M A lim F NoHeaderReceivedRecvHdrChunkEnv

/-- Envelope-parametric relocatable contract for `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`)
    wrapped with `withLsCodeRoLoaded lsmpl`. -/
def NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress)
    (Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_369 (Rust.withPanics ext))
    (blkPl_369).base
    (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpecOfEnv M A lim F Env))

/-- Canonical budget-threaded relocatable contract for `<NoHeaderReceived>::recv_hdr_chunk`
    (Block `369`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
abbrev NoHeaderReceivedRecvHdrChunkPlacedOkX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (ext : String → Option (State → State)) : Prop :=
  NoHeaderReceivedRecvHdrChunkPlacedOkXOfEnv M A lim F NoHeaderReceivedRecvHdrChunkEnv ext

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
