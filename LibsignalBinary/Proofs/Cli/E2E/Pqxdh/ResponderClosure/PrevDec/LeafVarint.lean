/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5

@[expose] public section

set_option autoImplicit false

/-!
# Handshake `decode_varint [local#5]` Re-exports

Re-exports the handshake `decode_varint::<&mut &[u8]> [local#5]` contract from `SpqrH.DecodeVarint5`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  decodeVarint5Name
  decodeVarint5_fnOff
  decodeVarint2Stack
  decodeVarint2StackX
  decodeVarint2Spec
  decodeVarint2SpecX
  DecodeVarint5OkExtX
  decodeVarint5_add_from_eq_fnAddr
  decodeVarint5_add_slow_eq_fnAddr
  decodeVarint5_ok_of_contracts_x
  decodeVarint5_ok_ext_x
  dv5_decodeErrorFrom_of_alloc
  decodeVarint5_ok
  bm6_decodeVarint5_of_alloc
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
