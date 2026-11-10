/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafReserve
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Handshake `finish_grow [local#9]` and `do_reserve [local#8]` Re-exports

Re-exports the `[LibsignalPlacement]` contracts for `finish_grow [local#9]` and
`do_reserve_and_handle [local#8]` from `SpqrH.DoReserve10Placed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  FinishGrow11PlacedOkExt
  DoReserve10PlacedOkExtX
  DoReserve10VecPlacedOkExtX
  finish_grow_11_placed_ok
  finish_grow_11_placed_ok_ext
  do_reserve_10_placed_ok
  do_reserve_10_vec1_placed_ok
  do_reserve_10_placed_ok_ext_x
  do_reserve_10_vec_placed_ok_ext_x
  doReserve10_placed_ok
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
