/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.NextChunkCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Relocatable Specification (Block `416`)

Relocatable `[LibsignalPlacement]` specification (`polyNextChunkPlacedSpec`) and contract
(`PolyNextChunkPlacedOkExt`) for `<PolyEncoder as Encoder>::next_chunk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

/-- Relocatable `[LibsignalPlacement]` separation-logic specification for
    `<PolyEncoder as Encoder>::next_chunk` (Block `416`):
    given `x8 = outA` (`34` bytes for `Chunk`) and `x0 = encA` (`&mut PolyEncoder`),
    when `enc.nextChunk = .ok (enc', chunk)`, updates `encA` in place to `polyEncoderAt A encA enc'`
    and writes `chunkAt outA chunk`, or panics on out-of-memory (`allocFailedIn`). -/
def polyNextChunkPlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec PolyNextChunkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A x.encA x.enc ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s.sp polyNextChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkAt x.outA x.chunk ∗
      polyEncoderAt A x.encA x.enc' ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗ stackAt s0.sp polyNextChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable `[LibsignalPlacement]` contract for `<PolyEncoder as Encoder>::next_chunk`
    (Block `416`) wrapped with `withLsCodeRoLoaded lsmpl`. -/
def PolyNextChunkPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
    (blkPl_416).base
    (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A))

end CryptoVerification.SpqrV1.Poly.NextChunk

namespace CryptoVerification.SpqrV1.Poly
export NextChunk (polyNextChunkPlacedSpec PolyNextChunkPlacedOkExt)
end CryptoVerification.SpqrV1.Poly
