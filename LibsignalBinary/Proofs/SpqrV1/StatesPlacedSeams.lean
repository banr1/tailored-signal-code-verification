/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced

/-!
# Relocatable `[LibsignalPlacement]` Seams for `SpqrV1/States`

Public `[LibsignalPlacement]` specifications and `StatesPlacedSeams` bundle for `SpqrV1/States/{FromPb,Recv,Leaves}`
(Blocks `332`, `333`, `335`, `336`, `344`, `345`, `354`), consumed by `Top/Recv` and `Top/Send`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.Recv

/-! ## Cross-Block `withLsCodeRoLoaded` Transfer from `blockProgram` -/

theorem ls_subroutine_ok_of_blockProgram_cro [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide)
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns := by decide +kernel) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

theorem ls_subroutine_ok_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry spec :=
  hcallee.eq_blockProgram ▸ h

/-! ## Relocatable `[LibsignalPlacement]` Specifications for `States/Leaves` Send Chunks -/

/-- Relocatable specification of `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::send_ct1_chunk` (Block `344`). -/
def ekReceivedCt1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (EkReceivedCt1SampledSendCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (528 + chunkSize) ∗
      chunkedEkReceivedCt1SampledAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 960)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedEkReceivedCt1SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 528#64) x.chunk ∗
      memRegion x.stA 528 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 960)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ct::Ct2Sampled>::send_ct2_chunk` (Block `354`). -/
def ct2SampledSendCt2ChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct2SampledSendCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct2_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (456 + chunkSize) ∗
      chunkedCt2SampledAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 896)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt2SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 456#64) x.chunk ∗
      memRegion x.stA 456 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 896)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ek::HeaderSent>::send_ek_chunk` (Block `336`). -/
def headerSentSendEkChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (HeaderSentSendEkChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (880 + chunkSize) ∗
      chunkedHeaderSentAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 1328)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedHeaderSentAt A x.outA x.outSt ∗
      chunkAt (x.outA + 880#64) x.chunk ∗
      memRegion x.stA 880 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 1328)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ek::Ct1Received>::send_ek_chunk` (Block `345`). -/
def ct1ReceivedSendEkChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct1ReceivedSendEkChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ek_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (504 + chunkSize) ∗
      chunkedCt1ReceivedAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 944)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt1ReceivedAt A x.outA x.outSt ∗
      chunkAt (x.outA + 504#64) x.chunk ∗
      memRegion x.stA 504 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 944)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable specification of `<spqr::v1::chunked::send_ct::Ct1Sampled>::send_ct1_chunk` (Block `335`). -/
def ct1SampledSendCt1ChunkPlacedSpec [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) :
    Spec (Ct1SampledSendCt1ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.stA ∧
      x.st.send_ct1_chunk = .ok (x.outSt, x.chunk)⌝ ∗
      memRegion x.outA (928 + chunkSize) ∗
      chunkedCt1SampledAt A x.stA x.st ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp (polyNextChunkStack + 1376)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkedCt1SampledAt A x.outA x.outSt ∗
      chunkAt (x.outA + 928#64) x.chunk ∗
      memRegion x.stA 928 ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp (polyNextChunkStack + 1376)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Per-Block Contract Predicates (`*PlacedOkX`) -/

/-- Block `333`: `<States>::from_pb` meets `withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX A F)`. -/
def StatesFromPbPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 333 (Rust.withPanics ext))
    (lsmpl.base 333) (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX A F))

/-- Block `332`: `<States>::recv` meets `withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K)`. -/
def StatesRecvPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 332 (Rust.withPanics ext))
    (lsmpl.base 332) (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K))

/-- Block `336`: `<HeaderSent>::send_ek_chunk` meets `withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec A F)`. -/
def HeaderSentSendEkChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 336 (Rust.withPanics ext))
    (lsmpl.base 336) (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec A F))

/-- Block `345`: `<Ct1Received>::send_ek_chunk` meets `withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec A F)`. -/
def Ct1ReceivedSendEkChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 345 (Rust.withPanics ext))
    (lsmpl.base 345) (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec A F))

/-- Block `335`: `<Ct1Sampled>::send_ct1_chunk` meets `withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec A F)`. -/
def Ct1SampledSendCt1ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 335 (Rust.withPanics ext))
    (lsmpl.base 335) (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec A F))

/-- Block `344`: `<EkReceivedCt1Sampled>::send_ct1_chunk` meets `withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec A F)`. -/
def EkReceivedCt1SampledSendCt1ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 344 (Rust.withPanics ext))
    (lsmpl.base 344) (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec A F))

/-- Block `354`: `<Ct2Sampled>::send_ct2_chunk` meets `withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec A F)`. -/
def Ct2SampledSendCt2ChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (libsignalSessionLib.blockProgram lsmpl 354 (Rust.withPanics ext))
    (lsmpl.base 354) (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec A F))

/-! ## Public Seam Bundle (`StatesPlacedSeams`) & Caller-Block Transfer Helpers -/

/-- Public `[LibsignalPlacement]` seam bundle for `SpqrV1/States/{FromPb,Recv,Leaves}`. -/
structure StatesPlacedSeams [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  statesFromPb_ok : StatesFromPbPlacedOkX A F ext
  statesRecv_ok : StatesRecvPlacedOkX A F K ext
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkPlacedOkX A F ext
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkPlacedOkX A F ext
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkPlacedOkX A F ext
  ekReceivedCt1SampledSendCt1Chunk_ok : EkReceivedCt1SampledSendCt1ChunkPlacedOkX A F ext
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkPlacedOkX A F ext

namespace StatesPlacedSeams

variable [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress} {K : MlKem}
  {ext : String → Option (State → State)}

theorem statesFromPb_on (h : StatesPlacedSeams A F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 333) (withLsCodeRoLoaded lsmpl (statesFromPbPlacedSpecX A F)) :=
  ls_subroutine_ok_of_blockProgram_cro h.statesFromPb_ok hi

theorem statesRecv_on (h : StatesPlacedSeams A F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 332) (withLsCodeRoLoaded lsmpl (statesRecvPlacedSpec A F K)) :=
  ls_subroutine_ok_of_blockProgram_cro h.statesRecv_ok hi

theorem headerSentSendEkChunk_on (h : StatesPlacedSeams A F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 336) (withLsCodeRoLoaded lsmpl (headerSentSendEkChunkPlacedSpec A F)) :=
  ls_subroutine_ok_of_blockProgram_cro h.headerSentSendEkChunk_ok hi

theorem ct1ReceivedSendEkChunk_on (h : StatesPlacedSeams A F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 345) (withLsCodeRoLoaded lsmpl (ct1ReceivedSendEkChunkPlacedSpec A F)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ct1ReceivedSendEkChunk_ok hi

theorem ct1SampledSendCt1Chunk_on (h : StatesPlacedSeams A F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 335) (withLsCodeRoLoaded lsmpl (ct1SampledSendCt1ChunkPlacedSpec A F)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ct1SampledSendCt1Chunk_ok hi

theorem ekReceivedCt1SampledSendCt1Chunk_on (h : StatesPlacedSeams A F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 344) (withLsCodeRoLoaded lsmpl (ekReceivedCt1SampledSendCt1ChunkPlacedSpec A F)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ekReceivedCt1SampledSendCt1Chunk_ok hi

theorem ct2SampledSendCt2Chunk_on (h : StatesPlacedSeams A F K ext)
    {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 354) (withLsCodeRoLoaded lsmpl (ct2SampledSendCt2ChunkPlacedSpec A F)) :=
  ls_subroutine_ok_of_blockProgram_cro h.ct2SampledSendCt2Chunk_ok hi

end StatesPlacedSeams

end CryptoVerification.SpqrV1
