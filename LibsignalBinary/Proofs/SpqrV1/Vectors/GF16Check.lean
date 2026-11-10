/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Proofs.SpqrV1.Vectors.GF16
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.GF16
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16

/-!
# Differential Vector Checks for `GF16.lean`

Checks `GF16.lean` against `Vectors/GF16.lean` (`gf16EdgeVectors`, `gf16RandomVectors`,
`reduceBytesTable`, `parallelMultVectors`) via `decide +kernel` and `#guard`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Vectors.GF16Check

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Vectors.GF16

def checkGF16Entry (e : GF16Entry) : Bool :=
  (GF16.add ⟨e.a⟩ ⟨e.b⟩).value == e.add &&
  (GF16.sub ⟨e.a⟩ ⟨e.b⟩).value == e.add &&
  unaccelerated.polyMul e.a e.b == e.polyMul &&
  reduce.polyReduce e.polyMul == e.mul &&
  unaccelerated.mul e.a e.b == e.mul &&
  (GF16.mul ⟨e.a⟩ ⟨e.b⟩).value == e.mul &&
  (GF16.divImpl ⟨e.a⟩ ⟨e.b⟩).value == e.div &&
  (GF16.div ⟨e.a⟩ ⟨e.b⟩).value == e.div &&
  (GF16.constDiv ⟨e.a⟩ ⟨e.b⟩).value == e.div

/-- Kernel-checked `REDUCE_BYTES` table equality (`256` entries). -/
theorem gf16ReduceBytesTable_ok :
    reduce.REDUCE_BYTES = reduceBytesTable := by
  decide +kernel

/-- Kernel-checked validation on the first 16 edge vectors (including `0`, `1`, `2`, `0xffff`). -/
theorem gf16EdgeVectors_head_ok :
    (gf16EdgeVectors.take 16).all checkGF16Entry = true := by
  decide +kernel

-- Full differential vector suite checked via `#guard` (228 edge + 200 random + 6 parallel_mult):
#guard gf16EdgeVectors.all checkGF16Entry
#guard gf16RandomVectors.all checkGF16Entry
#guard parallelMultVectors.all fun v =>
  (parallelMult ⟨v.scalar⟩ (v.input.map GF16.mk)).map GF16.value == v.output

end CryptoVerification.SpqrV1.Vectors.GF16Check
