/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Phase23

@[expose] public section

set_option autoImplicit false

/-!
# Handshake `bytes::merge [local#6]` Phases 2 and 3 Kit Re-export

Re-exports `PrevDec.SpqrH.BytesMerge6Phase23` for `VerNe.Chain3`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  epilogue6_err_0x07c
  epilogue6_decodeErrorFrom_0x074
  epilogue6_vtableDrop_0x254
  phase3_6_from_0x230
  phase3_6_from_0x210
  phase2_6_from_0x1b8
  phase2_6_from_0x0e4_nonempty
  phase2_6_from_0x094
)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit
