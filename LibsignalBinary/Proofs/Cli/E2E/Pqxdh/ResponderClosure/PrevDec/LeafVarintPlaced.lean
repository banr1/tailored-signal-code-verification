/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafVarint
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Handshake `decode_varint [local#4]` Re-exports

Re-exports the `[LibsignalPlacement]` contract for `decode_varint::<&mut &[u8]> [local#4]` from
`SpqrH.DecodeVarint5Placed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  DecodeVarint5PlacedOkExtX
  decodeErrorFromSpecWithStack_lscl_le
  dv5_decodeErrorFrom_placed_of_alloc
  dv5_decodeVarintSlow_placed_of_alloc
  decodeVarint5_placed_ok_of_contracts_x
  decodeVarint5_placed_ok
  decodeVarint5_placed_ok_cl
  decodeVarint5_placed_ok_ext_x
  bm6_decodeVarint5_placed_of_alloc
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
