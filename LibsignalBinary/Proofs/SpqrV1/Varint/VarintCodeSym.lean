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
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym -- shake: keep

/-!
# Relocatable Per-Block Fetches for `SpqrV1/Varint`

Provides relocatable instruction fetches for `encode_repeated` (`[local#1, 2]`),
`encode_varint` (`[local#2, 4]`), `decode_varint [local#2]`, and `skip_field [local#3]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

gen_ls_blk 145
gen_ls_blk 148
gen_ls_blk 263
gen_ls_blk 289
gen_ls_blk 291
gen_ls_blk 292

end CryptoVerification
