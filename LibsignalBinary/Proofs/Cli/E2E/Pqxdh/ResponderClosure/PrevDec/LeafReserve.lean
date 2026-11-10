/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10

/-!
# Handshake `finish_grow [local#11]` and `do_reserve [local#10]` Re-exports

Re-exports `finish_grow_11_ok_ext`, `do_reserve_10_vec_ok_ext_x`, and `do_reserve_10_ok_ext_x`
from `SpqrH.DoReserve10` under `PrevDec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  fnAddr_rel64
  finishGrow11Name
  doReserve10Name
  doReserve1VecSpecX
  DoReserve10OkExtX
  DoReserve10VecOkExtX
  finish_grow_11_ok_ext
  do_reserve_10_vec_ok_ext_x
  do_reserve_10_ok_ext_x
  doReserve10_ok
  c3_stage1Alloc_of_allocContractsX
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
