/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1Placed

/-!
# Relocatable `encode_repeated [local#3]` (Block `448`) & Exact-Capacity `PolynomialEncoder::encode [local#3]` (Block `456`)

Re-exports `encode_repeated_1_59_placed_ok{_x}` (Block `448`) and
`encode_polyEncoder_1_exact_pinned_placed_ok{_x}` (Block `456`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

abbrev encode_repeated_1_59_placed_ok :=
  @CryptoVerification.Cli.SpqrV1.Varint.encode_repeated_1_59_placed_ok

abbrev encode_repeated_1_59_placed_ok_x :=
  @CryptoVerification.Cli.SpqrV1.Varint.encode_repeated_1_59_placed_ok_x

abbrev encode_polyEncoder_1_exact_pinned_placed_ok :=
  @CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_polyEncoder_1_exact_pinned_placed_ok

abbrev encode_polyEncoder_1_exact_pinned_placed_ok_x :=
  @CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.encode_polyEncoder_1_exact_pinned_placed_ok_x

end CryptoVerification.Cli.SpqrV1.Top.Send
