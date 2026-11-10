/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Proof
public import LibsignalBinary.Proofs.Common.SharedHelpers

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Loop Re-Exports for `<PolyDecoder as Decoder>::add_chunk`

Re-exports `call_grow_one_pt_full_wpp_4k`, `call_grow_one_pt_empty_wpp_4k`, and
`bsearchReplace_wpp_4k` from `AddChunk.Proof`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopExt

export CryptoVerification.SpqrV1.Poly.AddChunk
  (call_grow_one_pt_full_wpp_4k call_grow_one_pt_empty_wpp_4k bsearchReplace_wpp_4k)

end LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.LoopExt
