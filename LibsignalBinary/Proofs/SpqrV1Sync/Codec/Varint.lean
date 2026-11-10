/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.VarintPure
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof

set_option autoImplicit false

/-!
# `Proto.decodeVarint` Round-Trip

Re-exports `LibsignalBinary.Proofs.SpqrV1Sync.Codec.VarintPure` and proves
`proto_decodeVarint_encodeVarint`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint

theorem proto_decodeVarint_encodeVarint (v : BitVec 64) (rest : Bytes) :
    Proto.decodeVarint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  have h1 := CryptoVerification.SpqrV1.Prost.BytesMerge.proto_decodeVarint_toOption
    (Proto.encodeVarint v ++ rest)
  rw [CryptoVerification.SpqrV1.Auth.protoEncodeVarint_eq_codec v,
    CryptoVerification.LibsignalProtoCodec.decodeVarint_encodeVarint] at h1
  rw [CryptoVerification.SpqrV1.Auth.protoEncodeVarint_eq_codec v]
  revert h1
  generalize Proto.decodeVarint (CryptoVerification.LibsignalProtoCodec.encodeVarint v ++ rest) = r
  cases r <;> simp [Except.toOption]


end CryptoVerification.SpqrV1Sync.Codec
