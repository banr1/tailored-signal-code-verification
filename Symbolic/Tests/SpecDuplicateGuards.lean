/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.ByteSpecs
public import Symbolic.Specifications.Model.Composed
public import Symbolic.Specifications.Refinement.WireFormat
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire

/-!
# Definitional Equality Guards for Specification Duplicates

Checks via `rfl` that deliberate duplicate definitions across the symbolic and binary specification
layers remain definitionally equal:
- Pure SHA-256 and HMAC-SHA256 definitions in `ByteSpecs` and `CryptoGames.HMAC` (duplicated so
  symbolic statement roots do not import `CryptoGames`).
- `PQXDH.x25519LowOrder` and `TripleRatchet.x25519LowOrder` under `Composed.HasExecBytes`.
- The SPQR varint length bound across `WireFormat`, `LibsignalSpqr`, and `LibsignalSpqrV1`
  (recursive varint decoders and nominal `MsgPreamble` wrappers differ in compilation or return
  type, so their agreement is proved propositionally in `LibsignalSpqrV1/Wire.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Tests.SpecDuplicateGuards

theorem shaState_eq : ByteSpecs.ShaState = CryptoGames.HMAC.ShaState := rfl

theorem sha256IV_eq : ByteSpecs.sha256IV = CryptoGames.HMAC.sha256IV := rfl

theorem toBEBytes_eq : @ByteSpecs.toBEBytes = @CryptoGames.HMAC.toBEBytes := rfl

theorem sha256Pad_eq : ByteSpecs.sha256Pad = CryptoGames.HMAC.sha256Pad := rfl

theorem chunks64_eq : ByteSpecs.chunks64 = CryptoGames.HMAC.chunks64 := rfl

theorem sha256With_eq : ByteSpecs.sha256With = CryptoGames.HMAC.sha256With := rfl

theorem hmacWith_eq : ByteSpecs.hmacWith = CryptoGames.HMAC.hmacWith := rfl

section X25519LowOrder

open scoped DY.Libsignal.Composed

theorem x25519LowOrder_eq [DY.Libsignal.Composed.HasExecBytes] :
    DY.Libsignal.PQXDH.x25519LowOrder = DY.Libsignal.TripleRatchet.x25519LowOrder :=
  rfl

end X25519LowOrder

theorem spqrMaxVarintBytes_eq_libsignalSpqr :
    DY.Libsignal.PQXDH.Refinement.spqrMaxVarintBytes =
      CryptoVerification.LibsignalSpqr.maxVarintBytes :=
  rfl

theorem spqrMaxVarintBytes_eq_spqrV1 :
    DY.Libsignal.PQXDH.Refinement.spqrMaxVarintBytes =
      CryptoVerification.LibsignalSpqrV1.MAX_VARINT_BYTES_LEN :=
  rfl

end Symbolic.Tests.SpecDuplicateGuards
