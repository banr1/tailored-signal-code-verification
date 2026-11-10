/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Leaf

@[expose] public section

set_option autoImplicit false

/-!
# Handshake `skip_field [local#6]` Re-export

Re-exports the handshake-unit `prost::encoding::skip_field [local#6]` contract for `PrevDec`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  skipField6Name
  skipField6_fnOff
  skipField3Stack
  skipField3Spec
  skipField3SpecAt
  SkipField6OkExtX
  skipField6_add_from_eq_fnAddr
  skipField6_add_varint_eq_fnAddr
  skipField6_ok_of_contracts
  skipField6_ok_ext
  skipField6_ok
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
