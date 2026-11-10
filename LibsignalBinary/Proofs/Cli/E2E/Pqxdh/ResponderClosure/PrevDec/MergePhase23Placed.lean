/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergePhase23
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Handshake `bytes::merge [local#5]` Phases 2 and 3 Re-exports

Re-exports the `[LibsignalPlacement]` Phase 2 and Phase 3 lemmas from
`PrevDec.SpqrH.BytesMerge6Phase23Placed`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  bytesMergeRawSpecXBoth
  MergePostXBoth
  MergePanicXBoth
  vecU8At_entails_existsBoth
  epilogue6_err_0x07c_placed
  epilogue6_decodeErrorFrom_0x074_placed
  epilogue6_vtableDrop_0x254_placed
  phase3_6_from_0x230_placed
  phase3_6_from_0x210_placed
  phase2_6_from_0x1b8_placed
  phase2_6_from_0x0e4_nonempty_placed
  phase2_6_from_0x094_placed
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
