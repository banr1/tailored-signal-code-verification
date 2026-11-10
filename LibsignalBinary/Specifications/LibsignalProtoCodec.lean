/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession -- shake: keep
public import LibsignalBinary.Specifications.LibsignalSignalMessage -- shake: keep

/-!
# Known-Answer Guards for `prost` Protobuf Encoding

**Checked by Lean.** Decidable regression tests pinning `protoSignalCodec` (`encodeVarint`,
`decodeVarint`, `encodeKey`, `encode`, and `decode` from `LibsignalSignalMessage.lean`) to known
protobuf wire encodings and `prost` test vectors.
-/

@[expose] public section

namespace CryptoVerification.LibsignalProtoCodec

open CryptoGames.LibsignalSession

private def bytes (l : List ℕ) : List (BitVec 8) := l.map (BitVec.ofNat 8)

-- `encode_varint` test vectors (`P/encoding/varint.rs:210–262`).
example : encodeVarint 300 = bytes [0xAC, 0x02] := by decide
example : encodeVarint 0 = bytes [0x00] := by decide
example : encodeVarint (BitVec.allOnes 64) =
    bytes [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x01] := by decide
example : decodeVarint (bytes [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x01]) =
    some (BitVec.allOnes 64, []) := by decide
-- `U64_MAX_PLUS_ONE` is rejected (`P/encoding/varint.rs:265–277`).
example : decodeVarint (bytes [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x02]) = none :=
  by decide
-- Non-minimal varints are accepted.
example : decodeVarint (bytes [0x80, 0x00, 0x07]) = some (0, bytes [0x07]) := by decide
-- Keys: `ratchet_key` = 0x0a, `counter` = 0x10, `addresses` = 0x32.
example : encodeKey 1 .lengthDelimited = bytes [0x0a] ∧ encodeKey 2 .varint = bytes [0x10] ∧
    encodeKey 6 .lengthDelimited = bytes [0x32] := by decide
-- A canonical message and its decoding.
example : encode { emptyProtoSignalMessage with ratchetKey := some (bytes [5, 6]), counter := some 300 } =
    bytes [0x0a, 0x02, 5, 6, 0x10, 0xAC, 0x02] := by decide
example : decode (bytes [0x0a, 0x02, 5, 6, 0x10, 0xAC, 0x02]) =
    some { emptyProtoSignalMessage with ratchetKey := some (bytes [5, 6]), counter := some 300 } := by decide
-- Last one wins; an unknown group (tag 7) is skipped; a wire-type mismatch and tag 0 are errors.
example : decode (bytes [0x10, 0x01, 0x3b, 0x08, 0x00, 0x3c, 0x10, 0x02]) =
    some { emptyProtoSignalMessage with counter := some 2 } := by decide
example : decode (bytes [0x12, 0x00]) = none ∧ decode (bytes [0x00, 0x00]) = none := by decide

end CryptoVerification.LibsignalProtoCodec
