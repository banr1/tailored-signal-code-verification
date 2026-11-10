/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.Placed.GenLsBlock -- shake: keep

/-!
# Relocatable Per-Block Instruction Fetches for Block `416`

Pre-extracted instruction-fetch table for `<PolyEncoder as Encoder>::next_chunk` (Block `416`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64.Obj

gen_ls_blk_poly 416

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_416 (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl
      "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk" =
      pl.base 416 :=
  ls_resolve_block (by decide +kernel)

end CryptoVerification
