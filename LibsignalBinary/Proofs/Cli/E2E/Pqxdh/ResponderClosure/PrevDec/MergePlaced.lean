/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Merge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePhase23Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Handshake `bytes::merge [local#5]` Re-exports

Re-exports `bytesMerge3RawSpecBoth`, `bytes_merge_6_*_placed_ok*`, and `BytesMerge6*Placed514OkExt`
from `PrevDec.SpqrH` under `PrevDec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  bytesMerge3RawSpecBoth
  MergePost3Both
  MergePanic3Both
  bytes_merge_6_both_placed_ok_of_contracts
  bytes_merge_6_placed_ok_of_contracts
  bytes_merge_6_proto_placed_ok_of_contracts
  bm6_decodeErrorFrom_placed_of_hooks
  bm6_decodeVarint5_placed_of_hooks
  bm6_vtableDrop_placed_of_dealloc
  bytes_merge_6_both_placed_ok
  bytes_merge_6_placed_ok
  bytes_merge_6_proto_placed_ok
  bytes_merge_6_cro_of_514
  subroutine_ok_withLsCl_of_cro
  bytes_merge_6_placed_ok_cro
  bytes_merge_6_proto_placed_ok_cro
  BytesMerge6Placed514OkExt
  BytesMerge6ProtoPlaced514OkExt
  bytesMerge6_placed_ok
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
