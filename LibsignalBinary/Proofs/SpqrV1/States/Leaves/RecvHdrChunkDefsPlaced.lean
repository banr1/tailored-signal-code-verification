/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesCodeSymB
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# `<NoHeaderReceived>::recv_hdr_chunk`: Relocatable Specifications (Block `369`)

Relocatable `[LibsignalPlacement]` specification (`noHeaderReceivedRecvHdrChunkPlacedSpec`),
contract abbreviation (`NoHeaderReceivedRecvHdrChunkPlacedOkX`), and `.rodata` loading lemma
(`rodata_hdrLabel_placed`) for Block `369`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.States.RecvCt2Chunk

/-- `.rodata` symbol for `Authenticator.hdrLabel` (`"Signal_PQCKA_V1_MLKEM768:ekheader"`, 33 bytes). -/
abbrev hdrLabelSym : String := "spqr:.rodata..Lanon.140"

/-- Relocatable specification of `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`). -/
def noHeaderReceivedRecvHdrChunkPlacedSpec [LibsignalPlacement]
    (F : ShaCompress) (A : RustAlloc) :
    Spec (NoHeaderReceivedRecvHdrChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_hdr⌝ ∗
      memRegion x.outA chunkedHeaderReceivedSize ∗
      chunkedNoHeaderReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt s.sp noHeaderReceivedRecvHdrChunkStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      noHeaderReceivedRecvChunkResultAt A x.outA (x.self.recv_hdr_chunk x.epoch x.chunk) ∗
      memRegion x.selfA chunkedNoHeaderReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt s0.sp noHeaderReceivedRecvHdrChunkStackX
  onPanic := fun x s0 sf =>
    ⌜((x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable contract for `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`)
    wrapped with `withLsCodeRoLoaded lsmpl`. -/
def NoHeaderReceivedRecvHdrChunkPlacedOkX [LibsignalPlacement]
    (F : ShaCompress) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_369 (Rust.withPanics ext))
    (blkPl_369).base
    (withLsCodeRoLoaded lsmpl (noHeaderReceivedRecvHdrChunkPlacedSpec F A))

/-- `.rodata` slice at `lsρ "spqr:.rodata..Lanon.140"` (`33` bytes): `Authenticator.hdrLabel`. -/
theorem rodata_hdrLabel_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ hdrLabelSym) ↦ᵣ Authenticator.hdrLabel) ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
