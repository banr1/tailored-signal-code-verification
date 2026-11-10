/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Relocatable Per-Block Fetches for `SpqrV1/Drop`

Per-block instruction fetch definitions for `libsignal_session` and `spqr` drop-glue blocks
(`132, 162, 165..167, 169..170, 264, 315..317, 320..338`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 132
gen_ls_blk 133
gen_ls_blk 136
gen_ls_blk 137
gen_ls_blk 138
gen_ls_blk 140
gen_ls_blk 141
gen_ls_blk 264
gen_ls_blk 265
gen_ls_blk 266
gen_ls_blk 267
gen_ls_blk 270
gen_ls_blk 271
gen_ls_blk 272
gen_ls_blk 273
gen_ls_blk 274
gen_ls_blk 275
gen_ls_blk 276
gen_ls_blk 277
gen_ls_blk 278
gen_ls_blk 279
gen_ls_blk 280
gen_ls_blk 281
gen_ls_blk 282
gen_ls_blk 283
gen_ls_blk 284
gen_ls_blk 285
gen_ls_blk 286

namespace SpqrV1.Drop.Blk337_338

gen_ls_blk 287
gen_ls_blk 288

end SpqrV1.Drop.Blk337_338

end CryptoVerification
