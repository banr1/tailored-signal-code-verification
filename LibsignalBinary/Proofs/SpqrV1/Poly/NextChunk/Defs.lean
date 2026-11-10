/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Canonical Specification

**Checked by Lean.**

AArch64 separation-logic specification (`polyNextChunkSpec`) for
`<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (`0x6a384`).
-/

@[expose] public section

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

abbrev polyNextChunkName : String :=
  "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"

@[simp, arm64_norm] theorem polyNextChunk_fnOff :
    libsignalSessionCode.fnOff polyNextChunkName =
      num% (ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk") :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"

/-- Stack budget for `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`):
    own frame (`0x60 + 0x450 = 1,200` bytes) + callee frame + `extHookStack` (`16,384` bytes). -/
abbrev polyNextChunkStack : Nat := 2048 + extHookStack

/-- Ghost arguments of `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`):
    - `x8 = outA` (`Chunk` sret output buffer, `chunkSize = 34` bytes)
    - `x0 = encA` (`&mut PolyEncoder`, `400` bytes) -/
structure PolyNextChunkGhost where
  outA : BitVec 64
  encA : BitVec 64
  enc : PolyEncoder
  enc' : PolyEncoder
  chunk : Chunk

/-- Separation-logic specification for `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`):
    given `x8 = outA` (`34` bytes for `Chunk`) and `x0 = encA` (`&mut PolyEncoder`),
    when `enc.nextChunk = .ok (enc', chunk)`, updates `encA` in place to `polyEncoderAt A encA enc'`
    and writes `chunkAt outA chunk`, or panics on out-of-memory (`allocFailedIn`). -/
def polyNextChunkSpec (A : RustAlloc) (b : BitVec 64) : Spec PolyNextChunkGhost where
  pre := fun x s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      s.readReg64 .x8 = x.outA ∧ s.readReg64 .x0 = x.encA ∧
      x.enc.nextChunk = .ok (x.enc', x.chunk)⌝ ∗
      memRegion x.outA chunkSize ∗
      polyEncoderAt A x.encA x.enc ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s.sp polyNextChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      chunkAt x.outA x.chunk ∗
      polyEncoderAt A x.encA x.enc' ∗
      tokenInitAt b ∗
      reduceTableAt b ∗
      A.pool ∗ stackAt s0.sp polyNextChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SpqrV1.Poly.NextChunk

namespace CryptoVerification.SpqrV1.Poly
export NextChunk (polyNextChunkName polyNextChunk_fnOff polyNextChunkStack PolyNextChunkGhost polyNextChunkSpec)
end CryptoVerification.SpqrV1.Poly
