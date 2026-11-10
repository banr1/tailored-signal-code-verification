/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.SkipField6
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Handshake `skip_field [local#5]` Re-export

Re-exports the `[LibsignalPlacement]` handshake `prost::encoding::skip_field [local#5]` contract.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  SkipField6PlacedOkExtX
  SkipField6Placed508OkExtX
  SkipField6AtPlacedOk
  skipField6_placed_of_at_depth
  skipField6_placed_ok_of_contracts
  skipField6_placed_ok
  skipField6_placed_ok_cl
  skipField6_placed_ok_ext_x
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
